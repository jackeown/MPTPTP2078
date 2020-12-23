%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:44 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   27 (  79 expanded)
%              Number of clauses        :   20 (  31 expanded)
%              Number of leaves         :    3 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :  125 ( 550 expanded)
%              Number of equality atoms :   14 (  69 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_wellord1(X1,X2)
        <=> ! [X3] :
              ~ ( r1_tarski(X3,X2)
                & X3 != k1_xboole_0
                & ! [X4] :
                    ~ ( r2_hidden(X4,X3)
                      & r1_xboole_0(k1_wellord1(X1,X4),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_wellord1)).

fof(d2_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_wellord1(X1)
      <=> ! [X2] :
            ~ ( r1_tarski(X2,k3_relat_1(X1))
              & X2 != k1_xboole_0
              & ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r1_xboole_0(k1_wellord1(X1,X3),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_wellord1)).

fof(t5_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_wellord1(X1)
      <=> r1_wellord1(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_wellord1)).

fof(c_0_3,plain,(
    ! [X10,X11,X12,X14,X16] :
      ( ( r2_hidden(esk3_3(X10,X11,X12),X12)
        | ~ r1_tarski(X12,X11)
        | X12 = k1_xboole_0
        | ~ r1_wellord1(X10,X11)
        | ~ v1_relat_1(X10) )
      & ( r1_xboole_0(k1_wellord1(X10,esk3_3(X10,X11,X12)),X12)
        | ~ r1_tarski(X12,X11)
        | X12 = k1_xboole_0
        | ~ r1_wellord1(X10,X11)
        | ~ v1_relat_1(X10) )
      & ( r1_tarski(esk4_2(X10,X14),X14)
        | r1_wellord1(X10,X14)
        | ~ v1_relat_1(X10) )
      & ( esk4_2(X10,X14) != k1_xboole_0
        | r1_wellord1(X10,X14)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(X16,esk4_2(X10,X14))
        | ~ r1_xboole_0(k1_wellord1(X10,X16),esk4_2(X10,X14))
        | r1_wellord1(X10,X14)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_wellord1])])])])])])).

fof(c_0_4,plain,(
    ! [X5,X6,X9] :
      ( ( r2_hidden(esk1_2(X5,X6),X6)
        | ~ r1_tarski(X6,k3_relat_1(X5))
        | X6 = k1_xboole_0
        | ~ v1_wellord1(X5)
        | ~ v1_relat_1(X5) )
      & ( r1_xboole_0(k1_wellord1(X5,esk1_2(X5,X6)),X6)
        | ~ r1_tarski(X6,k3_relat_1(X5))
        | X6 = k1_xboole_0
        | ~ v1_wellord1(X5)
        | ~ v1_relat_1(X5) )
      & ( r1_tarski(esk2_1(X5),k3_relat_1(X5))
        | v1_wellord1(X5)
        | ~ v1_relat_1(X5) )
      & ( esk2_1(X5) != k1_xboole_0
        | v1_wellord1(X5)
        | ~ v1_relat_1(X5) )
      & ( ~ r2_hidden(X9,esk2_1(X5))
        | ~ r1_xboole_0(k1_wellord1(X5,X9),esk2_1(X5))
        | v1_wellord1(X5)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_wellord1])])])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( v1_wellord1(X1)
        <=> r1_wellord1(X1,k3_relat_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t5_wellord1])).

cnf(c_0_6,plain,
    ( r1_wellord1(X2,X3)
    | ~ r2_hidden(X1,esk4_2(X2,X3))
    | ~ r1_xboole_0(k1_wellord1(X2,X1),esk4_2(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( r1_xboole_0(k1_wellord1(X1,esk1_2(X1,X2)),X2)
    | X2 = k1_xboole_0
    | ~ r1_tarski(X2,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | X2 = k1_xboole_0
    | ~ r1_tarski(X2,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( r1_wellord1(X1,X2)
    | esk4_2(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & ( ~ v1_wellord1(esk5_0)
      | ~ r1_wellord1(esk5_0,k3_relat_1(esk5_0)) )
    & ( v1_wellord1(esk5_0)
      | r1_wellord1(esk5_0,k3_relat_1(esk5_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_11,plain,
    ( r1_wellord1(X1,X2)
    | ~ r1_tarski(esk4_2(X1,X2),k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8]),c_0_9])).

cnf(c_0_12,plain,
    ( r1_tarski(esk4_2(X1,X2),X2)
    | r1_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_13,plain,
    ( v1_wellord1(X2)
    | ~ r2_hidden(X1,esk2_1(X2))
    | ~ r1_xboole_0(k1_wellord1(X2,X1),esk2_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,plain,
    ( r1_xboole_0(k1_wellord1(X1,esk3_3(X1,X2,X3)),X3)
    | X3 = k1_xboole_0
    | ~ r1_tarski(X3,X2)
    | ~ r1_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_15,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k1_xboole_0
    | ~ r1_tarski(X3,X2)
    | ~ r1_wellord1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_16,plain,
    ( v1_wellord1(X1)
    | esk2_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_17,negated_conjecture,
    ( ~ v1_wellord1(esk5_0)
    | ~ r1_wellord1(esk5_0,k3_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r1_wellord1(X1,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( v1_wellord1(X1)
    | ~ r1_wellord1(X1,X2)
    | ~ r1_tarski(esk2_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_21,plain,
    ( r1_tarski(esk2_1(X1),k3_relat_1(X1))
    | v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_22,negated_conjecture,
    ( v1_wellord1(esk5_0)
    | r1_wellord1(esk5_0,k3_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_wellord1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_24,plain,
    ( v1_wellord1(X1)
    | ~ r1_wellord1(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r1_wellord1(esk5_0,k3_relat_1(esk5_0)) ),
    inference(sr,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_19])]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.13/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(d3_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_wellord1(X1,X2)<=>![X3]:~(((r1_tarski(X3,X2)&X3!=k1_xboole_0)&![X4]:~((r2_hidden(X4,X3)&r1_xboole_0(k1_wellord1(X1,X4),X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_wellord1)).
% 0.13/0.37  fof(d2_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v1_wellord1(X1)<=>![X2]:~(((r1_tarski(X2,k3_relat_1(X1))&X2!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X2)&r1_xboole_0(k1_wellord1(X1,X3),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_wellord1)).
% 0.13/0.37  fof(t5_wellord1, conjecture, ![X1]:(v1_relat_1(X1)=>(v1_wellord1(X1)<=>r1_wellord1(X1,k3_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_wellord1)).
% 0.13/0.37  fof(c_0_3, plain, ![X10, X11, X12, X14, X16]:(((r2_hidden(esk3_3(X10,X11,X12),X12)|(~r1_tarski(X12,X11)|X12=k1_xboole_0)|~r1_wellord1(X10,X11)|~v1_relat_1(X10))&(r1_xboole_0(k1_wellord1(X10,esk3_3(X10,X11,X12)),X12)|(~r1_tarski(X12,X11)|X12=k1_xboole_0)|~r1_wellord1(X10,X11)|~v1_relat_1(X10)))&(((r1_tarski(esk4_2(X10,X14),X14)|r1_wellord1(X10,X14)|~v1_relat_1(X10))&(esk4_2(X10,X14)!=k1_xboole_0|r1_wellord1(X10,X14)|~v1_relat_1(X10)))&(~r2_hidden(X16,esk4_2(X10,X14))|~r1_xboole_0(k1_wellord1(X10,X16),esk4_2(X10,X14))|r1_wellord1(X10,X14)|~v1_relat_1(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_wellord1])])])])])])).
% 0.13/0.37  fof(c_0_4, plain, ![X5, X6, X9]:(((r2_hidden(esk1_2(X5,X6),X6)|(~r1_tarski(X6,k3_relat_1(X5))|X6=k1_xboole_0)|~v1_wellord1(X5)|~v1_relat_1(X5))&(r1_xboole_0(k1_wellord1(X5,esk1_2(X5,X6)),X6)|(~r1_tarski(X6,k3_relat_1(X5))|X6=k1_xboole_0)|~v1_wellord1(X5)|~v1_relat_1(X5)))&(((r1_tarski(esk2_1(X5),k3_relat_1(X5))|v1_wellord1(X5)|~v1_relat_1(X5))&(esk2_1(X5)!=k1_xboole_0|v1_wellord1(X5)|~v1_relat_1(X5)))&(~r2_hidden(X9,esk2_1(X5))|~r1_xboole_0(k1_wellord1(X5,X9),esk2_1(X5))|v1_wellord1(X5)|~v1_relat_1(X5)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_wellord1])])])])])).
% 0.13/0.37  fof(c_0_5, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(v1_wellord1(X1)<=>r1_wellord1(X1,k3_relat_1(X1))))), inference(assume_negation,[status(cth)],[t5_wellord1])).
% 0.13/0.37  cnf(c_0_6, plain, (r1_wellord1(X2,X3)|~r2_hidden(X1,esk4_2(X2,X3))|~r1_xboole_0(k1_wellord1(X2,X1),esk4_2(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.37  cnf(c_0_7, plain, (r1_xboole_0(k1_wellord1(X1,esk1_2(X1,X2)),X2)|X2=k1_xboole_0|~r1_tarski(X2,k3_relat_1(X1))|~v1_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.37  cnf(c_0_8, plain, (r2_hidden(esk1_2(X1,X2),X2)|X2=k1_xboole_0|~r1_tarski(X2,k3_relat_1(X1))|~v1_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.37  cnf(c_0_9, plain, (r1_wellord1(X1,X2)|esk4_2(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.37  fof(c_0_10, negated_conjecture, (v1_relat_1(esk5_0)&((~v1_wellord1(esk5_0)|~r1_wellord1(esk5_0,k3_relat_1(esk5_0)))&(v1_wellord1(esk5_0)|r1_wellord1(esk5_0,k3_relat_1(esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.13/0.37  cnf(c_0_11, plain, (r1_wellord1(X1,X2)|~r1_tarski(esk4_2(X1,X2),k3_relat_1(X1))|~v1_wellord1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_7]), c_0_8]), c_0_9])).
% 0.13/0.37  cnf(c_0_12, plain, (r1_tarski(esk4_2(X1,X2),X2)|r1_wellord1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.37  cnf(c_0_13, plain, (v1_wellord1(X2)|~r2_hidden(X1,esk2_1(X2))|~r1_xboole_0(k1_wellord1(X2,X1),esk2_1(X2))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.37  cnf(c_0_14, plain, (r1_xboole_0(k1_wellord1(X1,esk3_3(X1,X2,X3)),X3)|X3=k1_xboole_0|~r1_tarski(X3,X2)|~r1_wellord1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.37  cnf(c_0_15, plain, (r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k1_xboole_0|~r1_tarski(X3,X2)|~r1_wellord1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.37  cnf(c_0_16, plain, (v1_wellord1(X1)|esk2_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (~v1_wellord1(esk5_0)|~r1_wellord1(esk5_0,k3_relat_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_18, plain, (r1_wellord1(X1,k3_relat_1(X1))|~v1_wellord1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_20, plain, (v1_wellord1(X1)|~r1_wellord1(X1,X2)|~r1_tarski(esk2_1(X1),X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16])).
% 0.13/0.37  cnf(c_0_21, plain, (r1_tarski(esk2_1(X1),k3_relat_1(X1))|v1_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (v1_wellord1(esk5_0)|r1_wellord1(esk5_0,k3_relat_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (~v1_wellord1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.13/0.37  cnf(c_0_24, plain, (v1_wellord1(X1)|~r1_wellord1(X1,k3_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (r1_wellord1(esk5_0,k3_relat_1(esk5_0))), inference(sr,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_19])]), c_0_23]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 27
% 0.13/0.37  # Proof object clause steps            : 20
% 0.13/0.37  # Proof object formula steps           : 7
% 0.13/0.37  # Proof object conjectures             : 9
% 0.13/0.37  # Proof object clause conjectures      : 6
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 13
% 0.13/0.37  # Proof object initial formulas used   : 3
% 0.13/0.37  # Proof object generating inferences   : 6
% 0.13/0.37  # Proof object simplifying inferences  : 10
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 3
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 13
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 13
% 0.13/0.37  # Processed clauses                    : 20
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 1
% 0.13/0.37  # ...remaining for further processing  : 19
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 1
% 0.13/0.37  # Generated clauses                    : 11
% 0.13/0.37  # ...of the previous two non-trivial   : 8
% 0.13/0.37  # Contextual simplify-reflections      : 4
% 0.13/0.37  # Paramodulations                      : 10
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
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
% 0.13/0.37  # Current number of processed clauses  : 17
% 0.13/0.37  #    Positive orientable unit clauses  : 2
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 14
% 0.13/0.37  # Current number of unprocessed clauses: 1
% 0.13/0.37  # ...number of literals in the above   : 6
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 2
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 31
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 9
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 4
% 0.13/0.37  # Unit Clause-clause subsumption calls : 1
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 1
% 0.13/0.37  # BW rewrite match successes           : 1
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1170
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.026 s
% 0.13/0.37  # System time              : 0.005 s
% 0.13/0.37  # Total time               : 0.031 s
% 0.13/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
