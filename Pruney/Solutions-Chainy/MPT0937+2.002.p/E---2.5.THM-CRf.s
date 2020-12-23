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
% DateTime   : Thu Dec  3 11:00:40 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  63 expanded)
%              Number of clauses        :   16 (  28 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  104 ( 245 expanded)
%              Number of equality atoms :   23 (  54 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_wellord2,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k1_wellord2(X1)
      <=> ( k3_relat_1(X2) = X1
          & ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1) )
             => ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r1_tarski(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(t2_wellord2,conjecture,(
    ! [X1] : v1_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord2)).

fof(l1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> ! [X2] :
            ( r2_hidden(X2,k3_relat_1(X1))
           => r2_hidden(k4_tarski(X2,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_5,plain,(
    ! [X10,X11,X12,X13] :
      ( ( k3_relat_1(X11) = X10
        | X11 != k1_wellord2(X10)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(X12,X13),X11)
        | r1_tarski(X12,X13)
        | ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X13,X10)
        | X11 != k1_wellord2(X10)
        | ~ v1_relat_1(X11) )
      & ( ~ r1_tarski(X12,X13)
        | r2_hidden(k4_tarski(X12,X13),X11)
        | ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X13,X10)
        | X11 != k1_wellord2(X10)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk2_2(X10,X11),X10)
        | k3_relat_1(X11) != X10
        | X11 = k1_wellord2(X10)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk3_2(X10,X11),X10)
        | k3_relat_1(X11) != X10
        | X11 = k1_wellord2(X10)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X10,X11),esk3_2(X10,X11)),X11)
        | ~ r1_tarski(esk2_2(X10,X11),esk3_2(X10,X11))
        | k3_relat_1(X11) != X10
        | X11 = k1_wellord2(X10)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(esk2_2(X10,X11),esk3_2(X10,X11)),X11)
        | r1_tarski(esk2_2(X10,X11),esk3_2(X10,X11))
        | k3_relat_1(X11) != X10
        | X11 = k1_wellord2(X10)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_6,plain,(
    ! [X16] : v1_relat_1(k1_wellord2(X16)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] : v1_relat_2(k1_wellord2(X1)) ),
    inference(assume_negation,[status(cth)],[t2_wellord2])).

fof(c_0_8,plain,(
    ! [X7,X8] :
      ( ( ~ v1_relat_2(X7)
        | ~ r2_hidden(X8,k3_relat_1(X7))
        | r2_hidden(k4_tarski(X8,X8),X7)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(esk1_1(X7),k3_relat_1(X7))
        | v1_relat_2(X7)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(esk1_1(X7),esk1_1(X7)),X7)
        | v1_relat_2(X7)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).

cnf(c_0_9,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,negated_conjecture,(
    ~ v1_relat_2(k1_wellord2(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_12,plain,
    ( r2_hidden(esk1_1(X1),k3_relat_1(X1))
    | v1_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_9]),c_0_10])])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( ~ v1_relat_2(k1_wellord2(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_1(k1_wellord2(X1)),X1)
    | v1_relat_2(k1_wellord2(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_10]),c_0_13])).

fof(c_0_17,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_10])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk1_1(k1_wellord2(esk4_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( v1_relat_2(X1)
    | ~ r2_hidden(k4_tarski(esk1_1(X1),esk1_1(X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk1_1(k1_wellord2(esk4_0))),k1_wellord2(esk4_0))
    | ~ r2_hidden(X1,esk4_0)
    | ~ r1_tarski(X1,esk1_1(k1_wellord2(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( v1_relat_2(k1_wellord2(X1))
    | ~ r2_hidden(k4_tarski(esk1_1(k1_wellord2(X1)),esk1_1(k1_wellord2(X1))),k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_1(k1_wellord2(esk4_0)),esk1_1(k1_wellord2(esk4_0))),k1_wellord2(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_19]),c_0_23])])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_15]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:09:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.20/0.39  # and selection function SelectSmallestOrientable.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.033 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.20/0.39  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.20/0.39  fof(t2_wellord2, conjecture, ![X1]:v1_relat_2(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_wellord2)).
% 0.20/0.39  fof(l1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v1_relat_2(X1)<=>![X2]:(r2_hidden(X2,k3_relat_1(X1))=>r2_hidden(k4_tarski(X2,X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_wellord1)).
% 0.20/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.39  fof(c_0_5, plain, ![X10, X11, X12, X13]:(((k3_relat_1(X11)=X10|X11!=k1_wellord2(X10)|~v1_relat_1(X11))&((~r2_hidden(k4_tarski(X12,X13),X11)|r1_tarski(X12,X13)|(~r2_hidden(X12,X10)|~r2_hidden(X13,X10))|X11!=k1_wellord2(X10)|~v1_relat_1(X11))&(~r1_tarski(X12,X13)|r2_hidden(k4_tarski(X12,X13),X11)|(~r2_hidden(X12,X10)|~r2_hidden(X13,X10))|X11!=k1_wellord2(X10)|~v1_relat_1(X11))))&(((r2_hidden(esk2_2(X10,X11),X10)|k3_relat_1(X11)!=X10|X11=k1_wellord2(X10)|~v1_relat_1(X11))&(r2_hidden(esk3_2(X10,X11),X10)|k3_relat_1(X11)!=X10|X11=k1_wellord2(X10)|~v1_relat_1(X11)))&((~r2_hidden(k4_tarski(esk2_2(X10,X11),esk3_2(X10,X11)),X11)|~r1_tarski(esk2_2(X10,X11),esk3_2(X10,X11))|k3_relat_1(X11)!=X10|X11=k1_wellord2(X10)|~v1_relat_1(X11))&(r2_hidden(k4_tarski(esk2_2(X10,X11),esk3_2(X10,X11)),X11)|r1_tarski(esk2_2(X10,X11),esk3_2(X10,X11))|k3_relat_1(X11)!=X10|X11=k1_wellord2(X10)|~v1_relat_1(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.20/0.39  fof(c_0_6, plain, ![X16]:v1_relat_1(k1_wellord2(X16)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.20/0.39  fof(c_0_7, negated_conjecture, ~(![X1]:v1_relat_2(k1_wellord2(X1))), inference(assume_negation,[status(cth)],[t2_wellord2])).
% 0.20/0.39  fof(c_0_8, plain, ![X7, X8]:((~v1_relat_2(X7)|(~r2_hidden(X8,k3_relat_1(X7))|r2_hidden(k4_tarski(X8,X8),X7))|~v1_relat_1(X7))&((r2_hidden(esk1_1(X7),k3_relat_1(X7))|v1_relat_2(X7)|~v1_relat_1(X7))&(~r2_hidden(k4_tarski(esk1_1(X7),esk1_1(X7)),X7)|v1_relat_2(X7)|~v1_relat_1(X7)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).
% 0.20/0.39  cnf(c_0_9, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.39  cnf(c_0_10, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.39  fof(c_0_11, negated_conjecture, ~v1_relat_2(k1_wellord2(esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.20/0.39  cnf(c_0_12, plain, (r2_hidden(esk1_1(X1),k3_relat_1(X1))|v1_relat_2(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  cnf(c_0_13, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_9]), c_0_10])])).
% 0.20/0.39  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r1_tarski(X1,X2)|~r2_hidden(X1,X4)|~r2_hidden(X2,X4)|X3!=k1_wellord2(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.39  cnf(c_0_15, negated_conjecture, (~v1_relat_2(k1_wellord2(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_16, plain, (r2_hidden(esk1_1(k1_wellord2(X1)),X1)|v1_relat_2(k1_wellord2(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_10]), c_0_13])).
% 0.20/0.39  fof(c_0_17, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.39  cnf(c_0_18, plain, (r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_14]), c_0_10])])).
% 0.20/0.39  cnf(c_0_19, negated_conjecture, (r2_hidden(esk1_1(k1_wellord2(esk4_0)),esk4_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.39  cnf(c_0_20, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_21, plain, (v1_relat_2(X1)|~r2_hidden(k4_tarski(esk1_1(X1),esk1_1(X1)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  cnf(c_0_22, negated_conjecture, (r2_hidden(k4_tarski(X1,esk1_1(k1_wellord2(esk4_0))),k1_wellord2(esk4_0))|~r2_hidden(X1,esk4_0)|~r1_tarski(X1,esk1_1(k1_wellord2(esk4_0)))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.39  cnf(c_0_23, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_24, plain, (v1_relat_2(k1_wellord2(X1))|~r2_hidden(k4_tarski(esk1_1(k1_wellord2(X1)),esk1_1(k1_wellord2(X1))),k1_wellord2(X1))), inference(spm,[status(thm)],[c_0_21, c_0_10])).
% 0.20/0.39  cnf(c_0_25, negated_conjecture, (r2_hidden(k4_tarski(esk1_1(k1_wellord2(esk4_0)),esk1_1(k1_wellord2(esk4_0))),k1_wellord2(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_19]), c_0_23])])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_15]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 27
% 0.20/0.39  # Proof object clause steps            : 16
% 0.20/0.39  # Proof object formula steps           : 11
% 0.20/0.39  # Proof object conjectures             : 8
% 0.20/0.39  # Proof object clause conjectures      : 5
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 7
% 0.20/0.39  # Proof object initial formulas used   : 5
% 0.20/0.39  # Proof object generating inferences   : 6
% 0.20/0.39  # Proof object simplifying inferences  : 11
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 5
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 15
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 15
% 0.20/0.39  # Processed clauses                    : 43
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 0
% 0.20/0.39  # ...remaining for further processing  : 43
% 0.20/0.39  # Other redundant clauses eliminated   : 9
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 0
% 0.20/0.39  # Generated clauses                    : 24
% 0.20/0.39  # ...of the previous two non-trivial   : 17
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 15
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 9
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 20
% 0.20/0.39  #    Positive orientable unit clauses  : 5
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 1
% 0.20/0.39  #    Non-unit-clauses                  : 14
% 0.20/0.39  # Current number of unprocessed clauses: 1
% 0.20/0.39  # ...number of literals in the above   : 3
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 14
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 57
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 33
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.39  # Unit Clause-clause subsumption calls : 3
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 0
% 0.20/0.39  # BW rewrite match successes           : 0
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 1709
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.036 s
% 0.20/0.39  # System time              : 0.002 s
% 0.20/0.39  # Total time               : 0.038 s
% 0.20/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
