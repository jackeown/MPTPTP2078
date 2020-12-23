%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:24 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   28 (  55 expanded)
%              Number of clauses        :   19 (  22 expanded)
%              Number of leaves         :    4 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :  108 ( 225 expanded)
%              Number of equality atoms :   34 (  65 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(t117_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(c_0_4,plain,(
    ! [X11,X12,X13] :
      ( ( ~ r2_hidden(k4_tarski(X11,X12),X13)
        | r2_hidden(X12,k11_relat_1(X13,X11))
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(X12,k11_relat_1(X13,X11))
        | r2_hidden(k4_tarski(X11,X12),X13)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

fof(c_0_5,plain,(
    ! [X4,X5,X6,X7,X8,X9] :
      ( ( ~ r2_hidden(X6,X5)
        | X6 = X4
        | X5 != k1_tarski(X4) )
      & ( X7 != X4
        | r2_hidden(X7,X5)
        | X5 != k1_tarski(X4) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | esk1_2(X8,X9) != X8
        | X9 = k1_tarski(X8) )
      & ( r2_hidden(esk1_2(X8,X9),X9)
        | esk1_2(X8,X9) = X8
        | X9 = k1_tarski(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_6,plain,(
    ! [X14,X15,X16] :
      ( ( r2_hidden(X14,k1_relat_1(X16))
        | ~ r2_hidden(k4_tarski(X14,X15),X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( X15 = k1_funct_1(X16,X14)
        | ~ r2_hidden(k4_tarski(X14,X15),X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(X14,k1_relat_1(X16))
        | X15 != k1_funct_1(X16,X14)
        | r2_hidden(k4_tarski(X14,X15),X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_7,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( esk1_2(X1,k11_relat_1(X2,X3)) = X1
    | k11_relat_1(X2,X3) = k1_tarski(X1)
    | r2_hidden(k4_tarski(X3,esk1_2(X1,k11_relat_1(X2,X3))),X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r2_hidden(X1,k1_relat_1(X2))
         => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t117_funct_1])).

cnf(c_0_12,plain,
    ( esk1_2(X1,k11_relat_1(X2,X3)) = k1_funct_1(X2,X3)
    | esk1_2(X1,k11_relat_1(X2,X3)) = X1
    | k11_relat_1(X2,X3) = k1_tarski(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r2_hidden(esk2_0,k1_relat_1(esk3_0))
    & k11_relat_1(esk3_0,esk2_0) != k1_tarski(k1_funct_1(esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_15,plain,
    ( esk1_2(X1,k11_relat_1(X2,X3)) = X1
    | k11_relat_1(X2,X3) = k1_tarski(X1)
    | k1_funct_1(X2,X3) != X1
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(ef,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk2_0,k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,plain,
    ( esk1_2(k1_funct_1(X1,X2),k11_relat_1(X1,X2)) = k1_funct_1(X1,X2)
    | k1_tarski(k1_funct_1(X1,X2)) = k11_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_0,k1_funct_1(esk3_0,esk2_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_24,plain,
    ( k1_tarski(k1_funct_1(X1,X2)) = k11_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k1_funct_1(X1,X2),k11_relat_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,esk2_0),k11_relat_1(esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_19])])).

cnf(c_0_26,negated_conjecture,
    ( k11_relat_1(esk3_0,esk2_0) != k1_tarski(k1_funct_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_18]),c_0_19])]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___024_B31_F1_PI_AE_Q4_CS_SP_S2S
% 0.13/0.37  # and selection function SelectNewComplexAHP.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 0.13/0.37  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.13/0.37  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.13/0.37  fof(t117_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>k11_relat_1(X2,X1)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 0.13/0.37  fof(c_0_4, plain, ![X11, X12, X13]:((~r2_hidden(k4_tarski(X11,X12),X13)|r2_hidden(X12,k11_relat_1(X13,X11))|~v1_relat_1(X13))&(~r2_hidden(X12,k11_relat_1(X13,X11))|r2_hidden(k4_tarski(X11,X12),X13)|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.13/0.37  fof(c_0_5, plain, ![X4, X5, X6, X7, X8, X9]:(((~r2_hidden(X6,X5)|X6=X4|X5!=k1_tarski(X4))&(X7!=X4|r2_hidden(X7,X5)|X5!=k1_tarski(X4)))&((~r2_hidden(esk1_2(X8,X9),X9)|esk1_2(X8,X9)!=X8|X9=k1_tarski(X8))&(r2_hidden(esk1_2(X8,X9),X9)|esk1_2(X8,X9)=X8|X9=k1_tarski(X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.13/0.37  fof(c_0_6, plain, ![X14, X15, X16]:(((r2_hidden(X14,k1_relat_1(X16))|~r2_hidden(k4_tarski(X14,X15),X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(X15=k1_funct_1(X16,X14)|~r2_hidden(k4_tarski(X14,X15),X16)|(~v1_relat_1(X16)|~v1_funct_1(X16))))&(~r2_hidden(X14,k1_relat_1(X16))|X15!=k1_funct_1(X16,X14)|r2_hidden(k4_tarski(X14,X15),X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.13/0.37  cnf(c_0_7, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.37  cnf(c_0_8, plain, (r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_9, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_10, plain, (esk1_2(X1,k11_relat_1(X2,X3))=X1|k11_relat_1(X2,X3)=k1_tarski(X1)|r2_hidden(k4_tarski(X3,esk1_2(X1,k11_relat_1(X2,X3))),X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.13/0.37  fof(c_0_11, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>k11_relat_1(X2,X1)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t117_funct_1])).
% 0.13/0.37  cnf(c_0_12, plain, (esk1_2(X1,k11_relat_1(X2,X3))=k1_funct_1(X2,X3)|esk1_2(X1,k11_relat_1(X2,X3))=X1|k11_relat_1(X2,X3)=k1_tarski(X1)|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.13/0.37  cnf(c_0_13, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  fof(c_0_14, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(r2_hidden(esk2_0,k1_relat_1(esk3_0))&k11_relat_1(esk3_0,esk2_0)!=k1_tarski(k1_funct_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.13/0.37  cnf(c_0_15, plain, (esk1_2(X1,k11_relat_1(X2,X3))=X1|k11_relat_1(X2,X3)=k1_tarski(X1)|k1_funct_1(X2,X3)!=X1|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(ef,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_16, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (r2_hidden(esk2_0,k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_20, plain, (X2=k1_tarski(X1)|~r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_21, plain, (esk1_2(k1_funct_1(X1,X2),k11_relat_1(X1,X2))=k1_funct_1(X1,X2)|k1_tarski(k1_funct_1(X1,X2))=k11_relat_1(X1,X2)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_22, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (r2_hidden(k4_tarski(esk2_0,k1_funct_1(esk3_0,esk2_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19])])).
% 0.13/0.37  cnf(c_0_24, plain, (k1_tarski(k1_funct_1(X1,X2))=k11_relat_1(X1,X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k1_funct_1(X1,X2),k11_relat_1(X1,X2))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (r2_hidden(k1_funct_1(esk3_0,esk2_0),k11_relat_1(esk3_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_19])])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (k11_relat_1(esk3_0,esk2_0)!=k1_tarski(k1_funct_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_18]), c_0_19])]), c_0_26]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 28
% 0.13/0.37  # Proof object clause steps            : 19
% 0.13/0.37  # Proof object formula steps           : 9
% 0.13/0.37  # Proof object conjectures             : 10
% 0.13/0.37  # Proof object clause conjectures      : 7
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 10
% 0.13/0.37  # Proof object initial formulas used   : 4
% 0.13/0.37  # Proof object generating inferences   : 9
% 0.13/0.37  # Proof object simplifying inferences  : 9
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 4
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 13
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 13
% 0.13/0.37  # Processed clauses                    : 37
% 0.13/0.37  # ...of these trivial                  : 1
% 0.13/0.37  # ...subsumed                          : 1
% 0.13/0.37  # ...remaining for further processing  : 35
% 0.13/0.37  # Other redundant clauses eliminated   : 4
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 46
% 0.13/0.37  # ...of the previous two non-trivial   : 34
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 34
% 0.13/0.37  # Factorizations                       : 4
% 0.13/0.37  # Equation resolutions                 : 8
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 34
% 0.13/0.37  #    Positive orientable unit clauses  : 6
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 27
% 0.13/0.37  # Current number of unprocessed clauses: 10
% 0.13/0.37  # ...number of literals in the above   : 58
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 0
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 70
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 26
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.37  # Unit Clause-clause subsumption calls : 1
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 0
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1949
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.027 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.033 s
% 0.13/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
