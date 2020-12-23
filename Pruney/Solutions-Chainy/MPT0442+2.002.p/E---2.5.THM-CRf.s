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
% DateTime   : Thu Dec  3 10:48:14 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 118 expanded)
%              Number of clauses        :   39 (  58 expanded)
%              Number of leaves         :    7 (  27 expanded)
%              Depth                    :   14
%              Number of atoms          :  152 ( 492 expanded)
%              Number of equality atoms :   30 (  78 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
                & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_relat_1])).

fof(c_0_8,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_9,plain,(
    ! [X22,X23] : r1_tarski(X22,k2_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_relat_1(esk7_0)
    & r1_tarski(esk6_0,esk7_0)
    & ( ~ r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk7_0))
      | ~ r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_18,plain,(
    ! [X24,X25,X26,X28,X29,X30,X31,X33] :
      ( ( ~ r2_hidden(X26,X25)
        | r2_hidden(k4_tarski(esk3_3(X24,X25,X26),X26),X24)
        | X25 != k2_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(X29,X28),X24)
        | r2_hidden(X28,X25)
        | X25 != k2_relat_1(X24) )
      & ( ~ r2_hidden(esk4_2(X30,X31),X31)
        | ~ r2_hidden(k4_tarski(X33,esk4_2(X30,X31)),X30)
        | X31 = k2_relat_1(X30) )
      & ( r2_hidden(esk4_2(X30,X31),X31)
        | r2_hidden(k4_tarski(esk5_2(X30,X31),esk4_2(X30,X31)),X30)
        | X31 = k2_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,X1),esk7_0)
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_21,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X16,X15)
        | r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | r2_hidden(X17,X15)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k2_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k2_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X20)
        | r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k2_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_22,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk6_0,k2_xboole_0(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(esk7_0,X2))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_23])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(esk3_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( X1 = k2_xboole_0(X2,X2)
    | r2_hidden(esk2_3(X2,X2,X1),X1)
    | r2_hidden(esk2_3(X2,X2,X1),X2) ),
    inference(ef,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(k2_xboole_0(esk7_0,X2)))
    | ~ r2_hidden(k4_tarski(X3,X1),esk6_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X1) = X1
    | r2_hidden(esk2_3(X1,X1,X1),X1) ),
    inference(ef,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(k2_xboole_0(esk7_0,X2)))
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_32])).

fof(c_0_35,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X1)
    | r2_hidden(esk2_3(X1,X2,X1),X2) ),
    inference(ef,[status(thm)],[c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_39,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X35)
      | ~ v1_relat_1(X36)
      | k1_relat_1(k2_xboole_0(X35,X36)) = k2_xboole_0(k1_relat_1(X35),k1_relat_1(X36)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relat_1])])])).

cnf(c_0_40,negated_conjecture,
    ( k2_xboole_0(X1,esk6_0) = X1
    | r2_hidden(esk2_3(X1,esk6_0,X1),esk7_0)
    | r2_hidden(esk2_3(X1,esk6_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk6_0),X1),k2_relat_1(esk7_0))
    | r1_tarski(k2_relat_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_17])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_38])).

cnf(c_0_43,plain,
    ( k1_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_45,negated_conjecture,
    ( k2_xboole_0(esk7_0,esk6_0) = esk7_0
    | r2_hidden(esk2_3(esk7_0,esk6_0,esk7_0),esk7_0) ),
    inference(ef,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk7_0))
    | ~ r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_41])).

cnf(c_0_48,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(k2_xboole_0(X2,X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( k2_xboole_0(esk7_0,esk6_0) = esk7_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47])])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51])]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:05:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.41  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.12/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.41  #
% 0.12/0.41  # Preprocessing time       : 0.028 s
% 0.12/0.41  
% 0.12/0.41  # Proof found!
% 0.12/0.41  # SZS status Theorem
% 0.12/0.41  # SZS output start CNFRefutation
% 0.12/0.41  fof(t25_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 0.12/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.41  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.12/0.41  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.12/0.41  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.12/0.41  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.12/0.41  fof(t13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relat_1)).
% 0.12/0.41  fof(c_0_7, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2))))))), inference(assume_negation,[status(cth)],[t25_relat_1])).
% 0.12/0.41  fof(c_0_8, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.41  fof(c_0_9, plain, ![X22, X23]:r1_tarski(X22,k2_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.12/0.41  fof(c_0_10, negated_conjecture, (v1_relat_1(esk6_0)&(v1_relat_1(esk7_0)&(r1_tarski(esk6_0,esk7_0)&(~r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk7_0))|~r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.12/0.41  cnf(c_0_11, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.41  cnf(c_0_12, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.41  cnf(c_0_13, negated_conjecture, (r1_tarski(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.41  cnf(c_0_14, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.41  cnf(c_0_15, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.12/0.41  cnf(c_0_16, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_11, c_0_13])).
% 0.12/0.41  cnf(c_0_17, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.41  fof(c_0_18, plain, ![X24, X25, X26, X28, X29, X30, X31, X33]:(((~r2_hidden(X26,X25)|r2_hidden(k4_tarski(esk3_3(X24,X25,X26),X26),X24)|X25!=k2_relat_1(X24))&(~r2_hidden(k4_tarski(X29,X28),X24)|r2_hidden(X28,X25)|X25!=k2_relat_1(X24)))&((~r2_hidden(esk4_2(X30,X31),X31)|~r2_hidden(k4_tarski(X33,esk4_2(X30,X31)),X30)|X31=k2_relat_1(X30))&(r2_hidden(esk4_2(X30,X31),X31)|r2_hidden(k4_tarski(esk5_2(X30,X31),esk4_2(X30,X31)),X30)|X31=k2_relat_1(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.12/0.41  cnf(c_0_19, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.41  cnf(c_0_20, negated_conjecture, (r2_hidden(esk1_2(esk6_0,X1),esk7_0)|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.41  fof(c_0_21, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X16,X15)|(r2_hidden(X16,X13)|r2_hidden(X16,X14))|X15!=k2_xboole_0(X13,X14))&((~r2_hidden(X17,X13)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))&(~r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))))&(((~r2_hidden(esk2_3(X18,X19,X20),X18)|~r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|~r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19)))&(r2_hidden(esk2_3(X18,X19,X20),X20)|(r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k2_xboole_0(X18,X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.12/0.41  cnf(c_0_22, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.41  cnf(c_0_23, negated_conjecture, (r1_tarski(esk6_0,k2_xboole_0(esk7_0,X1))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.41  cnf(c_0_24, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.41  cnf(c_0_25, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_22])).
% 0.12/0.41  cnf(c_0_26, negated_conjecture, (r2_hidden(X1,k2_xboole_0(esk7_0,X2))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_11, c_0_23])).
% 0.12/0.41  cnf(c_0_27, plain, (r2_hidden(k4_tarski(esk3_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.41  cnf(c_0_28, plain, (X1=k2_xboole_0(X2,X2)|r2_hidden(esk2_3(X2,X2,X1),X1)|r2_hidden(esk2_3(X2,X2,X1),X2)), inference(ef,[status(thm)],[c_0_24])).
% 0.12/0.41  cnf(c_0_29, negated_conjecture, (r2_hidden(X1,k2_relat_1(k2_xboole_0(esk7_0,X2)))|~r2_hidden(k4_tarski(X3,X1),esk6_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.41  cnf(c_0_30, plain, (r2_hidden(k4_tarski(esk3_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_27])).
% 0.12/0.41  cnf(c_0_31, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.41  cnf(c_0_32, plain, (k2_xboole_0(X1,X1)=X1|r2_hidden(esk2_3(X1,X1,X1),X1)), inference(ef,[status(thm)],[c_0_28])).
% 0.12/0.41  cnf(c_0_33, negated_conjecture, (r2_hidden(X1,k2_relat_1(k2_xboole_0(esk7_0,X2)))|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.41  cnf(c_0_34, plain, (k2_xboole_0(X1,X1)=X1), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_32])).
% 0.12/0.41  fof(c_0_35, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.12/0.41  cnf(c_0_36, plain, (k2_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),X1)|r2_hidden(esk2_3(X1,X2,X1),X2)), inference(ef,[status(thm)],[c_0_24])).
% 0.12/0.41  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,k2_relat_1(esk7_0))|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.41  cnf(c_0_38, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.41  fof(c_0_39, plain, ![X35, X36]:(~v1_relat_1(X35)|(~v1_relat_1(X36)|k1_relat_1(k2_xboole_0(X35,X36))=k2_xboole_0(k1_relat_1(X35),k1_relat_1(X36)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relat_1])])])).
% 0.12/0.41  cnf(c_0_40, negated_conjecture, (k2_xboole_0(X1,esk6_0)=X1|r2_hidden(esk2_3(X1,esk6_0,X1),esk7_0)|r2_hidden(esk2_3(X1,esk6_0,X1),X1)), inference(spm,[status(thm)],[c_0_16, c_0_36])).
% 0.12/0.41  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk6_0),X1),k2_relat_1(esk7_0))|r1_tarski(k2_relat_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_37, c_0_17])).
% 0.12/0.41  cnf(c_0_42, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_12, c_0_38])).
% 0.12/0.41  cnf(c_0_43, plain, (k1_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.41  cnf(c_0_44, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.41  cnf(c_0_45, negated_conjecture, (k2_xboole_0(esk7_0,esk6_0)=esk7_0|r2_hidden(esk2_3(esk7_0,esk6_0,esk7_0),esk7_0)), inference(ef,[status(thm)],[c_0_40])).
% 0.12/0.41  cnf(c_0_46, negated_conjecture, (~r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk7_0))|~r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.41  cnf(c_0_47, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_14, c_0_41])).
% 0.12/0.41  cnf(c_0_48, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(k2_xboole_0(X2,X1)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.12/0.41  cnf(c_0_49, negated_conjecture, (k2_xboole_0(esk7_0,esk6_0)=esk7_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_45])).
% 0.12/0.41  cnf(c_0_50, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.41  cnf(c_0_51, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.41  cnf(c_0_52, negated_conjecture, (~r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47])])).
% 0.12/0.41  cnf(c_0_53, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51])]), c_0_52]), ['proof']).
% 0.12/0.41  # SZS output end CNFRefutation
% 0.12/0.41  # Proof object total steps             : 54
% 0.12/0.41  # Proof object clause steps            : 39
% 0.12/0.41  # Proof object formula steps           : 15
% 0.12/0.41  # Proof object conjectures             : 21
% 0.12/0.41  # Proof object clause conjectures      : 18
% 0.12/0.41  # Proof object formula conjectures     : 3
% 0.12/0.41  # Proof object initial clauses used    : 15
% 0.12/0.41  # Proof object initial formulas used   : 7
% 0.12/0.41  # Proof object generating inferences   : 21
% 0.12/0.41  # Proof object simplifying inferences  : 10
% 0.12/0.41  # Training examples: 0 positive, 0 negative
% 0.12/0.41  # Parsed axioms                        : 7
% 0.12/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.41  # Initial clauses                      : 20
% 0.12/0.41  # Removed in clause preprocessing      : 0
% 0.12/0.41  # Initial clauses in saturation        : 20
% 0.12/0.41  # Processed clauses                    : 537
% 0.12/0.41  # ...of these trivial                  : 32
% 0.12/0.41  # ...subsumed                          : 323
% 0.12/0.41  # ...remaining for further processing  : 182
% 0.12/0.41  # Other redundant clauses eliminated   : 5
% 0.12/0.41  # Clauses deleted for lack of memory   : 0
% 0.12/0.41  # Backward-subsumed                    : 0
% 0.12/0.41  # Backward-rewritten                   : 5
% 0.12/0.41  # Generated clauses                    : 1793
% 0.12/0.41  # ...of the previous two non-trivial   : 1578
% 0.12/0.41  # Contextual simplify-reflections      : 2
% 0.12/0.41  # Paramodulations                      : 1754
% 0.12/0.41  # Factorizations                       : 34
% 0.12/0.41  # Equation resolutions                 : 5
% 0.12/0.41  # Propositional unsat checks           : 0
% 0.12/0.41  #    Propositional check models        : 0
% 0.12/0.41  #    Propositional check unsatisfiable : 0
% 0.12/0.41  #    Propositional clauses             : 0
% 0.12/0.41  #    Propositional clauses after purity: 0
% 0.12/0.41  #    Propositional unsat core size     : 0
% 0.12/0.41  #    Propositional preprocessing time  : 0.000
% 0.12/0.41  #    Propositional encoding time       : 0.000
% 0.12/0.41  #    Propositional solver time         : 0.000
% 0.12/0.41  #    Success case prop preproc time    : 0.000
% 0.12/0.41  #    Success case prop encoding time   : 0.000
% 0.12/0.41  #    Success case prop solver time     : 0.000
% 0.12/0.41  # Current number of processed clauses  : 172
% 0.12/0.41  #    Positive orientable unit clauses  : 34
% 0.12/0.41  #    Positive unorientable unit clauses: 1
% 0.12/0.41  #    Negative unit clauses             : 1
% 0.12/0.41  #    Non-unit-clauses                  : 136
% 0.12/0.41  # Current number of unprocessed clauses: 1056
% 0.12/0.41  # ...number of literals in the above   : 2887
% 0.12/0.41  # Current number of archived formulas  : 0
% 0.12/0.41  # Current number of archived clauses   : 5
% 0.12/0.41  # Clause-clause subsumption calls (NU) : 5943
% 0.12/0.41  # Rec. Clause-clause subsumption calls : 4628
% 0.12/0.41  # Non-unit clause-clause subsumptions  : 325
% 0.12/0.41  # Unit Clause-clause subsumption calls : 309
% 0.12/0.41  # Rewrite failures with RHS unbound    : 0
% 0.12/0.41  # BW rewrite match attempts            : 38
% 0.12/0.41  # BW rewrite match successes           : 6
% 0.12/0.41  # Condensation attempts                : 0
% 0.12/0.41  # Condensation successes               : 0
% 0.12/0.41  # Termbank termtop insertions          : 25684
% 0.12/0.41  
% 0.12/0.41  # -------------------------------------------------
% 0.12/0.41  # User time                : 0.057 s
% 0.12/0.41  # System time              : 0.011 s
% 0.12/0.41  # Total time               : 0.068 s
% 0.12/0.41  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
