%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:11 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 105 expanded)
%              Number of clauses        :   23 (  48 expanded)
%              Number of leaves         :    6 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  148 ( 396 expanded)
%              Number of equality atoms :   42 ( 112 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t204_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(c_0_6,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X9,X8)
        | X9 = X6
        | X9 = X7
        | X8 != k2_tarski(X6,X7) )
      & ( X10 != X6
        | r2_hidden(X10,X8)
        | X8 != k2_tarski(X6,X7) )
      & ( X10 != X7
        | r2_hidden(X10,X8)
        | X8 != k2_tarski(X6,X7) )
      & ( esk1_3(X11,X12,X13) != X11
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_tarski(X11,X12) )
      & ( esk1_3(X11,X12,X13) != X12
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_tarski(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X13)
        | esk1_3(X11,X12,X13) = X11
        | esk1_3(X11,X12,X13) = X12
        | X13 = k2_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_7,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_8,plain,(
    ! [X30,X31,X32,X34] :
      ( ( r2_hidden(esk5_3(X30,X31,X32),k1_relat_1(X32))
        | ~ r2_hidden(X30,k9_relat_1(X32,X31))
        | ~ v1_relat_1(X32) )
      & ( r2_hidden(k4_tarski(esk5_3(X30,X31,X32),X30),X32)
        | ~ r2_hidden(X30,k9_relat_1(X32,X31))
        | ~ v1_relat_1(X32) )
      & ( r2_hidden(esk5_3(X30,X31,X32),X31)
        | ~ r2_hidden(X30,k9_relat_1(X32,X31))
        | ~ v1_relat_1(X32) )
      & ( ~ r2_hidden(X34,k1_relat_1(X32))
        | ~ r2_hidden(k4_tarski(X34,X30),X32)
        | ~ r2_hidden(X34,X31)
        | r2_hidden(X30,k9_relat_1(X32,X31))
        | ~ v1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_9,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X28)
      | k11_relat_1(X28,X29) = k9_relat_1(X28,k1_tarski(X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_10,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_11,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( esk5_3(X1,k2_tarski(X2,X3),X4) = X3
    | esk5_3(X1,k2_tarski(X2,X3),X4) = X2
    | ~ v1_relat_1(X4)
    | ~ r2_hidden(X1,k9_relat_1(X4,k2_tarski(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k2_tarski(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
    ( esk5_3(X1,k2_tarski(X2,X2),X3) = X2
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k11_relat_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(k4_tarski(X1,X2),X3)
        <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t204_relat_1])).

fof(c_0_20,plain,(
    ! [X16,X17,X18,X19,X21,X22,X23,X24,X26] :
      ( ( r2_hidden(k4_tarski(esk2_4(X16,X17,X18,X19),X19),X16)
        | ~ r2_hidden(X19,X18)
        | X18 != k9_relat_1(X16,X17)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk2_4(X16,X17,X18,X19),X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k9_relat_1(X16,X17)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(X22,X21),X16)
        | ~ r2_hidden(X22,X17)
        | r2_hidden(X21,X18)
        | X18 != k9_relat_1(X16,X17)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(esk3_3(X16,X23,X24),X24)
        | ~ r2_hidden(k4_tarski(X26,esk3_3(X16,X23,X24)),X16)
        | ~ r2_hidden(X26,X23)
        | X24 = k9_relat_1(X16,X23)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(esk4_3(X16,X23,X24),esk3_3(X16,X23,X24)),X16)
        | r2_hidden(esk3_3(X16,X23,X24),X24)
        | X24 = k9_relat_1(X16,X23)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk4_3(X16,X23,X24),X23)
        | r2_hidden(esk3_3(X16,X23,X24),X24)
        | X24 = k9_relat_1(X16,X23)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X2,k9_relat_1(X3,k2_tarski(X1,X1)))
    | ~ r2_hidden(X2,k11_relat_1(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & ( ~ r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)
      | ~ r2_hidden(esk7_0,k11_relat_1(esk8_0,esk6_0)) )
    & ( r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)
      | r2_hidden(esk7_0,k11_relat_1(esk8_0,esk6_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X2,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X5 != k9_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X2,k11_relat_1(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)
    | r2_hidden(esk7_0,k11_relat_1(esk8_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,X1),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk7_0,k9_relat_1(esk8_0,X1))
    | ~ r2_hidden(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_26])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)
    | ~ r2_hidden(esk7_0,k11_relat_1(esk8_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk7_0,k11_relat_1(esk8_0,X1))
    | ~ r2_hidden(esk6_0,k2_tarski(X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_16]),c_0_26])])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k11_relat_1(esk8_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_28])])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:23:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.020 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.14/0.37  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.14/0.37  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 0.14/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.37  fof(t204_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 0.14/0.37  fof(d13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X5,X4),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 0.14/0.37  fof(c_0_6, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X9,X8)|(X9=X6|X9=X7)|X8!=k2_tarski(X6,X7))&((X10!=X6|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))&(X10!=X7|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))))&(((esk1_3(X11,X12,X13)!=X11|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12))&(esk1_3(X11,X12,X13)!=X12|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12)))&(r2_hidden(esk1_3(X11,X12,X13),X13)|(esk1_3(X11,X12,X13)=X11|esk1_3(X11,X12,X13)=X12)|X13=k2_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.14/0.37  cnf(c_0_7, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.37  fof(c_0_8, plain, ![X30, X31, X32, X34]:((((r2_hidden(esk5_3(X30,X31,X32),k1_relat_1(X32))|~r2_hidden(X30,k9_relat_1(X32,X31))|~v1_relat_1(X32))&(r2_hidden(k4_tarski(esk5_3(X30,X31,X32),X30),X32)|~r2_hidden(X30,k9_relat_1(X32,X31))|~v1_relat_1(X32)))&(r2_hidden(esk5_3(X30,X31,X32),X31)|~r2_hidden(X30,k9_relat_1(X32,X31))|~v1_relat_1(X32)))&(~r2_hidden(X34,k1_relat_1(X32))|~r2_hidden(k4_tarski(X34,X30),X32)|~r2_hidden(X34,X31)|r2_hidden(X30,k9_relat_1(X32,X31))|~v1_relat_1(X32))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.14/0.37  fof(c_0_9, plain, ![X28, X29]:(~v1_relat_1(X28)|k11_relat_1(X28,X29)=k9_relat_1(X28,k1_tarski(X29))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.14/0.37  fof(c_0_10, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.37  cnf(c_0_11, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_tarski(X3,X2))), inference(er,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_12, plain, (r2_hidden(esk5_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_13, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_14, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_15, plain, (esk5_3(X1,k2_tarski(X2,X3),X4)=X3|esk5_3(X1,k2_tarski(X2,X3),X4)=X2|~v1_relat_1(X4)|~r2_hidden(X1,k9_relat_1(X4,k2_tarski(X2,X3)))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.14/0.37  cnf(c_0_16, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k2_tarski(X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.37  cnf(c_0_17, plain, (r2_hidden(k4_tarski(esk5_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_18, plain, (esk5_3(X1,k2_tarski(X2,X2),X3)=X2|~v1_relat_1(X3)|~r2_hidden(X1,k11_relat_1(X3,X2))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.37  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1))))), inference(assume_negation,[status(cth)],[t204_relat_1])).
% 0.14/0.37  fof(c_0_20, plain, ![X16, X17, X18, X19, X21, X22, X23, X24, X26]:((((r2_hidden(k4_tarski(esk2_4(X16,X17,X18,X19),X19),X16)|~r2_hidden(X19,X18)|X18!=k9_relat_1(X16,X17)|~v1_relat_1(X16))&(r2_hidden(esk2_4(X16,X17,X18,X19),X17)|~r2_hidden(X19,X18)|X18!=k9_relat_1(X16,X17)|~v1_relat_1(X16)))&(~r2_hidden(k4_tarski(X22,X21),X16)|~r2_hidden(X22,X17)|r2_hidden(X21,X18)|X18!=k9_relat_1(X16,X17)|~v1_relat_1(X16)))&((~r2_hidden(esk3_3(X16,X23,X24),X24)|(~r2_hidden(k4_tarski(X26,esk3_3(X16,X23,X24)),X16)|~r2_hidden(X26,X23))|X24=k9_relat_1(X16,X23)|~v1_relat_1(X16))&((r2_hidden(k4_tarski(esk4_3(X16,X23,X24),esk3_3(X16,X23,X24)),X16)|r2_hidden(esk3_3(X16,X23,X24),X24)|X24=k9_relat_1(X16,X23)|~v1_relat_1(X16))&(r2_hidden(esk4_3(X16,X23,X24),X23)|r2_hidden(esk3_3(X16,X23,X24),X24)|X24=k9_relat_1(X16,X23)|~v1_relat_1(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).
% 0.14/0.37  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)|~r2_hidden(X2,k9_relat_1(X3,k2_tarski(X1,X1)))|~r2_hidden(X2,k11_relat_1(X3,X1))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.14/0.37  fof(c_0_22, negated_conjecture, (v1_relat_1(esk8_0)&((~r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)|~r2_hidden(esk7_0,k11_relat_1(esk8_0,esk6_0)))&(r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)|r2_hidden(esk7_0,k11_relat_1(esk8_0,esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.14/0.37  cnf(c_0_23, plain, (r2_hidden(X2,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X5!=k9_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.37  cnf(c_0_24, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)|~r2_hidden(X2,k11_relat_1(X3,X1))), inference(spm,[status(thm)],[c_0_21, c_0_16])).
% 0.14/0.37  cnf(c_0_25, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)|r2_hidden(esk7_0,k11_relat_1(esk8_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.37  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.37  cnf(c_0_27, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X4,X1),X2)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_23])).
% 0.14/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.14/0.37  cnf(c_0_29, negated_conjecture, (r2_hidden(esk7_0,k9_relat_1(esk8_0,X1))|~r2_hidden(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_26])])).
% 0.14/0.37  cnf(c_0_30, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.37  cnf(c_0_31, negated_conjecture, (~r2_hidden(k4_tarski(esk6_0,esk7_0),esk8_0)|~r2_hidden(esk7_0,k11_relat_1(esk8_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.37  cnf(c_0_32, negated_conjecture, (r2_hidden(esk7_0,k11_relat_1(esk8_0,X1))|~r2_hidden(esk6_0,k2_tarski(X1,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_16]), c_0_26])])).
% 0.14/0.37  cnf(c_0_33, plain, (r2_hidden(X1,k2_tarski(X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])])).
% 0.14/0.37  cnf(c_0_34, negated_conjecture, (~r2_hidden(esk7_0,k11_relat_1(esk8_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_28])])).
% 0.14/0.37  cnf(c_0_35, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 36
% 0.14/0.37  # Proof object clause steps            : 23
% 0.14/0.37  # Proof object formula steps           : 13
% 0.14/0.37  # Proof object conjectures             : 11
% 0.14/0.37  # Proof object clause conjectures      : 8
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 10
% 0.14/0.37  # Proof object initial formulas used   : 6
% 0.14/0.37  # Proof object generating inferences   : 8
% 0.14/0.37  # Proof object simplifying inferences  : 14
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 6
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 21
% 0.14/0.37  # Removed in clause preprocessing      : 1
% 0.14/0.37  # Initial clauses in saturation        : 20
% 0.14/0.37  # Processed clauses                    : 70
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 5
% 0.14/0.37  # ...remaining for further processing  : 65
% 0.14/0.37  # Other redundant clauses eliminated   : 8
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 2
% 0.14/0.37  # Backward-rewritten                   : 5
% 0.14/0.37  # Generated clauses                    : 109
% 0.14/0.37  # ...of the previous two non-trivial   : 102
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 103
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 8
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 33
% 0.14/0.37  #    Positive orientable unit clauses  : 5
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 1
% 0.14/0.37  #    Non-unit-clauses                  : 27
% 0.14/0.37  # Current number of unprocessed clauses: 70
% 0.14/0.37  # ...number of literals in the above   : 314
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 27
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 346
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 207
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 7
% 0.14/0.37  # Unit Clause-clause subsumption calls : 3
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 4
% 0.14/0.37  # BW rewrite match successes           : 2
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 3650
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.024 s
% 0.14/0.37  # System time              : 0.003 s
% 0.14/0.37  # Total time               : 0.027 s
% 0.14/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
