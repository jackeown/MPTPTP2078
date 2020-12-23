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
% DateTime   : Thu Dec  3 11:00:40 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   29 ( 114 expanded)
%              Number of clauses        :   18 (  51 expanded)
%              Number of leaves         :    5 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  109 ( 466 expanded)
%              Number of equality atoms :   18 (  98 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(t2_wellord2,conjecture,(
    ! [X1] : v1_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord2)).

fof(l1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> ! [X2] :
            ( r2_hidden(X2,k3_relat_1(X1))
           => r2_hidden(k4_tarski(X2,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_wellord1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_5,plain,(
    ! [X14,X15,X16,X17] :
      ( ( k3_relat_1(X15) = X14
        | X15 != k1_wellord2(X14)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(X16,X17),X15)
        | r1_tarski(X16,X17)
        | ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X17,X14)
        | X15 != k1_wellord2(X14)
        | ~ v1_relat_1(X15) )
      & ( ~ r1_tarski(X16,X17)
        | r2_hidden(k4_tarski(X16,X17),X15)
        | ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X17,X14)
        | X15 != k1_wellord2(X14)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(esk3_2(X14,X15),X14)
        | k3_relat_1(X15) != X14
        | X15 = k1_wellord2(X14)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(esk4_2(X14,X15),X14)
        | k3_relat_1(X15) != X14
        | X15 = k1_wellord2(X14)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X14,X15),esk4_2(X14,X15)),X15)
        | ~ r1_tarski(esk3_2(X14,X15),esk4_2(X14,X15))
        | k3_relat_1(X15) != X14
        | X15 = k1_wellord2(X14)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(esk3_2(X14,X15),esk4_2(X14,X15)),X15)
        | r1_tarski(esk3_2(X14,X15),esk4_2(X14,X15))
        | k3_relat_1(X15) != X14
        | X15 = k1_wellord2(X14)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_6,plain,(
    ! [X20] : v1_relat_1(k1_wellord2(X20)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] : v1_relat_2(k1_wellord2(X1)) ),
    inference(assume_negation,[status(cth)],[t2_wellord2])).

fof(c_0_8,plain,(
    ! [X11,X12] :
      ( ( ~ v1_relat_2(X11)
        | ~ r2_hidden(X12,k3_relat_1(X11))
        | r2_hidden(k4_tarski(X12,X12),X11)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk2_1(X11),k3_relat_1(X11))
        | v1_relat_2(X11)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(esk2_1(X11),esk2_1(X11)),X11)
        | v1_relat_2(X11)
        | ~ v1_relat_1(X11) ) ) ),
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
    ~ v1_relat_2(k1_wellord2(esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_12,plain,
    ( r2_hidden(esk2_1(X1),k3_relat_1(X1))
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
    ( ~ v1_relat_2(k1_wellord2(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v1_relat_2(k1_wellord2(X1))
    | r2_hidden(esk2_1(k1_wellord2(X1)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_10]),c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_10])])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk2_1(k1_wellord2(esk5_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_1(k1_wellord2(esk5_0))),k1_wellord2(esk5_0))
    | ~ r2_hidden(X1,esk5_0)
    | ~ r1_tarski(X1,esk2_1(k1_wellord2(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_20,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_1(k1_wellord2(esk5_0)),esk2_1(k1_wellord2(esk5_0))),k1_wellord2(esk5_0))
    | ~ r1_tarski(esk2_1(k1_wellord2(esk5_0)),esk2_1(k1_wellord2(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,plain,
    ( v1_relat_2(X1)
    | ~ r2_hidden(k4_tarski(esk2_1(X1),esk2_1(X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_2(esk2_1(k1_wellord2(esk5_0)),esk2_1(k1_wellord2(esk5_0))),esk2_1(k1_wellord2(esk5_0)))
    | r2_hidden(k4_tarski(esk2_1(k1_wellord2(esk5_0)),esk2_1(k1_wellord2(esk5_0))),k1_wellord2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( v1_relat_2(k1_wellord2(X1))
    | ~ r2_hidden(k4_tarski(esk2_1(k1_wellord2(X1)),esk2_1(k1_wellord2(X1))),k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_1(k1_wellord2(esk5_0)),esk2_1(k1_wellord2(esk5_0))),k1_wellord2(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_15]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.13/0.38  # and selection function SelectSmallestOrientable.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 0.13/0.38  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.13/0.38  fof(t2_wellord2, conjecture, ![X1]:v1_relat_2(k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_wellord2)).
% 0.13/0.38  fof(l1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v1_relat_2(X1)<=>![X2]:(r2_hidden(X2,k3_relat_1(X1))=>r2_hidden(k4_tarski(X2,X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_wellord1)).
% 0.13/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.38  fof(c_0_5, plain, ![X14, X15, X16, X17]:(((k3_relat_1(X15)=X14|X15!=k1_wellord2(X14)|~v1_relat_1(X15))&((~r2_hidden(k4_tarski(X16,X17),X15)|r1_tarski(X16,X17)|(~r2_hidden(X16,X14)|~r2_hidden(X17,X14))|X15!=k1_wellord2(X14)|~v1_relat_1(X15))&(~r1_tarski(X16,X17)|r2_hidden(k4_tarski(X16,X17),X15)|(~r2_hidden(X16,X14)|~r2_hidden(X17,X14))|X15!=k1_wellord2(X14)|~v1_relat_1(X15))))&(((r2_hidden(esk3_2(X14,X15),X14)|k3_relat_1(X15)!=X14|X15=k1_wellord2(X14)|~v1_relat_1(X15))&(r2_hidden(esk4_2(X14,X15),X14)|k3_relat_1(X15)!=X14|X15=k1_wellord2(X14)|~v1_relat_1(X15)))&((~r2_hidden(k4_tarski(esk3_2(X14,X15),esk4_2(X14,X15)),X15)|~r1_tarski(esk3_2(X14,X15),esk4_2(X14,X15))|k3_relat_1(X15)!=X14|X15=k1_wellord2(X14)|~v1_relat_1(X15))&(r2_hidden(k4_tarski(esk3_2(X14,X15),esk4_2(X14,X15)),X15)|r1_tarski(esk3_2(X14,X15),esk4_2(X14,X15))|k3_relat_1(X15)!=X14|X15=k1_wellord2(X14)|~v1_relat_1(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.13/0.38  fof(c_0_6, plain, ![X20]:v1_relat_1(k1_wellord2(X20)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.13/0.38  fof(c_0_7, negated_conjecture, ~(![X1]:v1_relat_2(k1_wellord2(X1))), inference(assume_negation,[status(cth)],[t2_wellord2])).
% 0.13/0.38  fof(c_0_8, plain, ![X11, X12]:((~v1_relat_2(X11)|(~r2_hidden(X12,k3_relat_1(X11))|r2_hidden(k4_tarski(X12,X12),X11))|~v1_relat_1(X11))&((r2_hidden(esk2_1(X11),k3_relat_1(X11))|v1_relat_2(X11)|~v1_relat_1(X11))&(~r2_hidden(k4_tarski(esk2_1(X11),esk2_1(X11)),X11)|v1_relat_2(X11)|~v1_relat_1(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).
% 0.13/0.38  cnf(c_0_9, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_10, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  fof(c_0_11, negated_conjecture, ~v1_relat_2(k1_wellord2(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.13/0.38  cnf(c_0_12, plain, (r2_hidden(esk2_1(X1),k3_relat_1(X1))|v1_relat_2(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_13, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_9]), c_0_10])])).
% 0.13/0.38  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r1_tarski(X1,X2)|~r2_hidden(X1,X4)|~r2_hidden(X2,X4)|X3!=k1_wellord2(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (~v1_relat_2(k1_wellord2(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_16, plain, (v1_relat_2(k1_wellord2(X1))|r2_hidden(esk2_1(k1_wellord2(X1)),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_10]), c_0_13])).
% 0.13/0.38  cnf(c_0_17, plain, (r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_14]), c_0_10])])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (r2_hidden(esk2_1(k1_wellord2(esk5_0)),esk5_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_1(k1_wellord2(esk5_0))),k1_wellord2(esk5_0))|~r2_hidden(X1,esk5_0)|~r1_tarski(X1,esk2_1(k1_wellord2(esk5_0)))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.38  fof(c_0_20, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (r2_hidden(k4_tarski(esk2_1(k1_wellord2(esk5_0)),esk2_1(k1_wellord2(esk5_0))),k1_wellord2(esk5_0))|~r1_tarski(esk2_1(k1_wellord2(esk5_0)),esk2_1(k1_wellord2(esk5_0)))), inference(spm,[status(thm)],[c_0_19, c_0_18])).
% 0.13/0.38  cnf(c_0_22, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_23, plain, (v1_relat_2(X1)|~r2_hidden(k4_tarski(esk2_1(X1),esk2_1(X1)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_24, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (r2_hidden(esk1_2(esk2_1(k1_wellord2(esk5_0)),esk2_1(k1_wellord2(esk5_0))),esk2_1(k1_wellord2(esk5_0)))|r2_hidden(k4_tarski(esk2_1(k1_wellord2(esk5_0)),esk2_1(k1_wellord2(esk5_0))),k1_wellord2(esk5_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.38  cnf(c_0_26, plain, (v1_relat_2(k1_wellord2(X1))|~r2_hidden(k4_tarski(esk2_1(k1_wellord2(X1)),esk2_1(k1_wellord2(X1))),k1_wellord2(X1))), inference(spm,[status(thm)],[c_0_23, c_0_10])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (r2_hidden(k4_tarski(esk2_1(k1_wellord2(esk5_0)),esk2_1(k1_wellord2(esk5_0))),k1_wellord2(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_21])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_15]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 29
% 0.13/0.38  # Proof object clause steps            : 18
% 0.13/0.38  # Proof object formula steps           : 11
% 0.13/0.38  # Proof object conjectures             : 10
% 0.13/0.38  # Proof object clause conjectures      : 7
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 8
% 0.13/0.38  # Proof object initial formulas used   : 5
% 0.13/0.38  # Proof object generating inferences   : 8
% 0.13/0.38  # Proof object simplifying inferences  : 9
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 5
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 15
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 15
% 0.13/0.38  # Processed clauses                    : 62
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 5
% 0.13/0.38  # ...remaining for further processing  : 57
% 0.13/0.38  # Other redundant clauses eliminated   : 7
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 3
% 0.13/0.38  # Generated clauses                    : 88
% 0.13/0.38  # ...of the previous two non-trivial   : 81
% 0.13/0.38  # Contextual simplify-reflections      : 1
% 0.13/0.38  # Paramodulations                      : 81
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 7
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 32
% 0.13/0.38  #    Positive orientable unit clauses  : 4
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 27
% 0.13/0.38  # Current number of unprocessed clauses: 42
% 0.13/0.38  # ...number of literals in the above   : 181
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 18
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 264
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 184
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 6
% 0.13/0.38  # Unit Clause-clause subsumption calls : 3
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 1
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3569
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.029 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.034 s
% 0.13/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
