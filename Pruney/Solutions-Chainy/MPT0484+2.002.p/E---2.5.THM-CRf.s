%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:26 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 133 expanded)
%              Number of clauses        :   33 (  57 expanded)
%              Number of leaves         :    7 (  31 expanded)
%              Depth                    :   18
%              Number of atoms          :  137 ( 402 expanded)
%              Number of equality atoms :   12 (  70 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(t76_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(t75_relat_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X4,k6_relat_1(X3)))
      <=> ( r2_hidden(X2,X3)
          & r2_hidden(k4_tarski(X1,X2),X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_relat_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(k2_relat_1(X2),X1)
         => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t79_relat_1])).

fof(c_0_8,plain,(
    ! [X27,X28] :
      ( ( r1_tarski(k5_relat_1(X28,k6_relat_1(X27)),X28)
        | ~ v1_relat_1(X28) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X27),X28),X28)
        | ~ v1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & r1_tarski(k2_relat_1(esk5_0),esk4_0)
    & k5_relat_1(esk5_0,k6_relat_1(esk4_0)) != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_11,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk5_0,k6_relat_1(X1)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_15,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_16,negated_conjecture,
    ( k5_relat_1(esk5_0,k6_relat_1(X1)) = esk5_0
    | ~ r1_tarski(esk5_0,k5_relat_1(esk5_0,k6_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( k5_relat_1(esk5_0,k6_relat_1(esk4_0)) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( k5_relat_1(esk5_0,k6_relat_1(X1)) = esk5_0
    | r2_hidden(esk1_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(X1))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_20,plain,(
    ! [X13,X14,X15,X16,X17] :
      ( ( ~ r1_tarski(X13,X14)
        | ~ r2_hidden(k4_tarski(X15,X16),X13)
        | r2_hidden(k4_tarski(X15,X16),X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk2_2(X13,X17),esk3_2(X13,X17)),X13)
        | r1_tarski(X13,X17)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X13,X17),esk3_2(X13,X17)),X17)
        | r1_tarski(X13,X17)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

fof(c_0_21,plain,(
    ! [X20,X21,X22] :
      ( ( r2_hidden(X20,k1_relat_1(X22))
        | ~ r2_hidden(k4_tarski(X20,X21),X22)
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(X21,k2_relat_1(X22))
        | ~ r2_hidden(k4_tarski(X20,X21),X22)
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

cnf(c_0_22,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0))),X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_2(esk5_0,X1),esk3_2(esk5_0,X1)),esk5_0)
    | r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk5_0))
    | ~ r2_hidden(k4_tarski(X2,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_12])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_2(esk5_0,X1),esk3_2(esk5_0,X1)),esk5_0)
    | r2_hidden(esk1_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0))),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0))),X1)
    | r2_hidden(esk3_2(esk5_0,X1),k2_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0))),k2_relat_1(esk5_0))
    | r1_tarski(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_33,plain,(
    ! [X23,X24,X25,X26] :
      ( ( r2_hidden(X24,X25)
        | ~ r2_hidden(k4_tarski(X23,X24),k5_relat_1(X26,k6_relat_1(X25)))
        | ~ v1_relat_1(X26) )
      & ( r2_hidden(k4_tarski(X23,X24),X26)
        | ~ r2_hidden(k4_tarski(X23,X24),k5_relat_1(X26,k6_relat_1(X25)))
        | ~ v1_relat_1(X26) )
      & ( ~ r2_hidden(X24,X25)
        | ~ r2_hidden(k4_tarski(X23,X24),X26)
        | r2_hidden(k4_tarski(X23,X24),k5_relat_1(X26,k6_relat_1(X25)))
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t75_relat_1])])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0))),k2_relat_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_32]),c_0_14])]),c_0_18])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,k6_relat_1(X2)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X4)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0))),X1)
    | ~ r1_tarski(k2_relat_1(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(esk5_0,k6_relat_1(X3)))
    | ~ r2_hidden(k4_tarski(X1,X2),esk5_0)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0))),esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( k5_relat_1(esk5_0,k6_relat_1(X1)) = esk5_0
    | r2_hidden(k4_tarski(esk2_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(X1))),esk3_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(X1)))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_27])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk3_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0)))),k5_relat_1(esk5_0,k6_relat_1(esk4_0)))
    | ~ r2_hidden(k4_tarski(X1,esk3_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0)))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0))),esk3_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0)))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | ~ r2_hidden(k4_tarski(esk2_2(esk5_0,X1),esk3_2(esk5_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0))),esk3_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0)))),k5_relat_1(esk5_0,k6_relat_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_46]),c_0_14])]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:57:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.20/0.41  # and selection function SelectSmallestOrientable.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.030 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t79_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k5_relat_1(X2,k6_relat_1(X1))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 0.20/0.41  fof(t76_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 0.20/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.41  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 0.20/0.41  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 0.20/0.41  fof(t75_relat_1, axiom, ![X1, X2, X3, X4]:(v1_relat_1(X4)=>(r2_hidden(k4_tarski(X1,X2),k5_relat_1(X4,k6_relat_1(X3)))<=>(r2_hidden(X2,X3)&r2_hidden(k4_tarski(X1,X2),X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_relat_1)).
% 0.20/0.41  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k5_relat_1(X2,k6_relat_1(X1))=X2))), inference(assume_negation,[status(cth)],[t79_relat_1])).
% 0.20/0.41  fof(c_0_8, plain, ![X27, X28]:((r1_tarski(k5_relat_1(X28,k6_relat_1(X27)),X28)|~v1_relat_1(X28))&(r1_tarski(k5_relat_1(k6_relat_1(X27),X28),X28)|~v1_relat_1(X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).
% 0.20/0.41  fof(c_0_9, negated_conjecture, (v1_relat_1(esk5_0)&(r1_tarski(k2_relat_1(esk5_0),esk4_0)&k5_relat_1(esk5_0,k6_relat_1(esk4_0))!=esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.20/0.41  fof(c_0_10, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.41  cnf(c_0_11, plain, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.41  cnf(c_0_12, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_13, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_14, negated_conjecture, (r1_tarski(k5_relat_1(esk5_0,k6_relat_1(X1)),esk5_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.41  fof(c_0_15, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.41  cnf(c_0_16, negated_conjecture, (k5_relat_1(esk5_0,k6_relat_1(X1))=esk5_0|~r1_tarski(esk5_0,k5_relat_1(esk5_0,k6_relat_1(X1)))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.41  cnf(c_0_17, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_18, negated_conjecture, (k5_relat_1(esk5_0,k6_relat_1(esk4_0))!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_19, negated_conjecture, (k5_relat_1(esk5_0,k6_relat_1(X1))=esk5_0|r2_hidden(esk1_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(X1))),esk5_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.41  fof(c_0_20, plain, ![X13, X14, X15, X16, X17]:((~r1_tarski(X13,X14)|(~r2_hidden(k4_tarski(X15,X16),X13)|r2_hidden(k4_tarski(X15,X16),X14))|~v1_relat_1(X13))&((r2_hidden(k4_tarski(esk2_2(X13,X17),esk3_2(X13,X17)),X13)|r1_tarski(X13,X17)|~v1_relat_1(X13))&(~r2_hidden(k4_tarski(esk2_2(X13,X17),esk3_2(X13,X17)),X17)|r1_tarski(X13,X17)|~v1_relat_1(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.20/0.41  fof(c_0_21, plain, ![X20, X21, X22]:((r2_hidden(X20,k1_relat_1(X22))|~r2_hidden(k4_tarski(X20,X21),X22)|~v1_relat_1(X22))&(r2_hidden(X21,k2_relat_1(X22))|~r2_hidden(k4_tarski(X20,X21),X22)|~v1_relat_1(X22))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.20/0.41  cnf(c_0_22, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_23, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0))),esk5_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.41  cnf(c_0_24, plain, (r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_25, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.41  cnf(c_0_26, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0))),X1)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.41  cnf(c_0_27, negated_conjecture, (r2_hidden(k4_tarski(esk2_2(esk5_0,X1),esk3_2(esk5_0,X1)),esk5_0)|r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_24, c_0_12])).
% 0.20/0.41  cnf(c_0_28, negated_conjecture, (r2_hidden(X1,k2_relat_1(esk5_0))|~r2_hidden(k4_tarski(X2,X1),esk5_0)), inference(spm,[status(thm)],[c_0_25, c_0_12])).
% 0.20/0.41  cnf(c_0_29, negated_conjecture, (r2_hidden(k4_tarski(esk2_2(esk5_0,X1),esk3_2(esk5_0,X1)),esk5_0)|r2_hidden(esk1_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0))),X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.41  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_31, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0))),X1)|r2_hidden(esk3_2(esk5_0,X1),k2_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.41  cnf(c_0_32, negated_conjecture, (r2_hidden(esk3_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0))),k2_relat_1(esk5_0))|r1_tarski(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.41  fof(c_0_33, plain, ![X23, X24, X25, X26]:(((r2_hidden(X24,X25)|~r2_hidden(k4_tarski(X23,X24),k5_relat_1(X26,k6_relat_1(X25)))|~v1_relat_1(X26))&(r2_hidden(k4_tarski(X23,X24),X26)|~r2_hidden(k4_tarski(X23,X24),k5_relat_1(X26,k6_relat_1(X25)))|~v1_relat_1(X26)))&(~r2_hidden(X24,X25)|~r2_hidden(k4_tarski(X23,X24),X26)|r2_hidden(k4_tarski(X23,X24),k5_relat_1(X26,k6_relat_1(X25)))|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t75_relat_1])])])).
% 0.20/0.41  cnf(c_0_34, negated_conjecture, (r2_hidden(esk3_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0))),k2_relat_1(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_32]), c_0_14])]), c_0_18])).
% 0.20/0.41  cnf(c_0_35, plain, (r2_hidden(k4_tarski(X3,X1),k5_relat_1(X4,k6_relat_1(X2)))|~r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),X4)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.41  cnf(c_0_36, negated_conjecture, (r2_hidden(esk3_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0))),X1)|~r1_tarski(k2_relat_1(esk5_0),X1)), inference(spm,[status(thm)],[c_0_22, c_0_34])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (r1_tarski(k2_relat_1(esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),k5_relat_1(esk5_0,k6_relat_1(X3)))|~r2_hidden(k4_tarski(X1,X2),esk5_0)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_35, c_0_12])).
% 0.20/0.41  cnf(c_0_39, negated_conjecture, (r2_hidden(esk3_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0))),esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.41  cnf(c_0_40, negated_conjecture, (k5_relat_1(esk5_0,k6_relat_1(X1))=esk5_0|r2_hidden(k4_tarski(esk2_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(X1))),esk3_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(X1)))),esk5_0)), inference(spm,[status(thm)],[c_0_16, c_0_27])).
% 0.20/0.41  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_42, negated_conjecture, (r2_hidden(k4_tarski(X1,esk3_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0)))),k5_relat_1(esk5_0,k6_relat_1(esk4_0)))|~r2_hidden(k4_tarski(X1,esk3_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0)))),esk5_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.41  cnf(c_0_43, negated_conjecture, (r2_hidden(k4_tarski(esk2_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0))),esk3_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0)))),esk5_0)), inference(spm,[status(thm)],[c_0_18, c_0_40])).
% 0.20/0.41  cnf(c_0_44, negated_conjecture, (r1_tarski(esk5_0,X1)|~r2_hidden(k4_tarski(esk2_2(esk5_0,X1),esk3_2(esk5_0,X1)),X1)), inference(spm,[status(thm)],[c_0_41, c_0_12])).
% 0.20/0.41  cnf(c_0_45, negated_conjecture, (r2_hidden(k4_tarski(esk2_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0))),esk3_2(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0)))),k5_relat_1(esk5_0,k6_relat_1(esk4_0)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.41  cnf(c_0_46, negated_conjecture, (r1_tarski(esk5_0,k5_relat_1(esk5_0,k6_relat_1(esk4_0)))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_46]), c_0_14])]), c_0_18]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 48
% 0.20/0.41  # Proof object clause steps            : 33
% 0.20/0.41  # Proof object formula steps           : 15
% 0.20/0.41  # Proof object conjectures             : 27
% 0.20/0.41  # Proof object clause conjectures      : 24
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 12
% 0.20/0.41  # Proof object initial formulas used   : 7
% 0.20/0.41  # Proof object generating inferences   : 21
% 0.20/0.41  # Proof object simplifying inferences  : 6
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 7
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 19
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 19
% 0.20/0.41  # Processed clauses                    : 190
% 0.20/0.41  # ...of these trivial                  : 1
% 0.20/0.41  # ...subsumed                          : 48
% 0.20/0.41  # ...remaining for further processing  : 141
% 0.20/0.41  # Other redundant clauses eliminated   : 18
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 2
% 0.20/0.41  # Backward-rewritten                   : 2
% 0.20/0.41  # Generated clauses                    : 1645
% 0.20/0.41  # ...of the previous two non-trivial   : 1461
% 0.20/0.41  # Contextual simplify-reflections      : 0
% 0.20/0.41  # Paramodulations                      : 1627
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 18
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 118
% 0.20/0.41  #    Positive orientable unit clauses  : 12
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 1
% 0.20/0.41  #    Non-unit-clauses                  : 105
% 0.20/0.41  # Current number of unprocessed clauses: 1295
% 0.20/0.41  # ...number of literals in the above   : 5204
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 21
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 1675
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 1176
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 49
% 0.20/0.41  # Unit Clause-clause subsumption calls : 31
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 10
% 0.20/0.41  # BW rewrite match successes           : 2
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 32000
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.062 s
% 0.20/0.41  # System time              : 0.003 s
% 0.20/0.41  # Total time               : 0.064 s
% 0.20/0.41  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
