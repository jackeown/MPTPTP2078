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
% DateTime   : Thu Dec  3 10:45:57 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 411 expanded)
%              Number of clauses        :   31 ( 197 expanded)
%              Number of leaves         :    9 (  99 expanded)
%              Depth                    :   13
%              Number of atoms          :  119 (1060 expanded)
%              Number of equality atoms :   37 ( 357 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(X2,k3_subset_1(X1,X2))
      <=> X2 = k1_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ( r1_tarski(X2,k3_subset_1(X1,X2))
        <=> X2 = k1_subset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t38_subset_1])).

fof(c_0_10,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))
    & ( ~ r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
      | esk6_0 != k1_subset_1(esk5_0) )
    & ( r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
      | esk6_0 = k1_subset_1(esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_11,plain,(
    ! [X34] : k1_subset_1(X34) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_12,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k4_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_13,plain,(
    ! [X22,X23] : k4_xboole_0(X22,X23) = k5_xboole_0(X22,k3_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_14,negated_conjecture,
    ( ~ r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
    | esk6_0 != k1_subset_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X20] :
      ( X20 = k1_xboole_0
      | r2_hidden(esk3_1(X20),X20) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_17,plain,(
    ! [X25,X26] :
      ( ( ~ r1_xboole_0(X25,X26)
        | k4_xboole_0(X25,X26) = X25 )
      & ( k4_xboole_0(X25,X26) != X25
        | r1_xboole_0(X25,X26) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | ~ r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X24] : r1_xboole_0(X24,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_25,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk3_1(esk6_0),esk6_0)
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(esk5_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_2(k1_xboole_0,k3_subset_1(esk5_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(esk3_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_33,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | k3_subset_1(X35,X36) = k4_xboole_0(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk3_1(esk6_0),esk6_0)
    | ~ r2_hidden(esk1_2(k1_xboole_0,k3_subset_1(esk5_0,k1_xboole_0)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))
    | esk6_0 = k1_subset_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk3_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_15])).

cnf(c_0_39,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_41,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_1(k1_xboole_0),k1_xboole_0)
    | r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(esk3_1(esk6_0),k5_xboole_0(X1,k3_xboole_0(X1,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk6_0)) = k3_subset_1(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,k3_subset_1(esk5_0,esk6_0))
    | r2_hidden(esk3_1(k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( ~ r2_hidden(esk3_1(esk6_0),k3_subset_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk3_1(k1_xboole_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_37]),c_0_46])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(esk3_1(k1_xboole_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_47]),c_0_32])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_47,c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 16:43:47 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 0.14/0.37  # and selection function SelectCQIArEqFirst.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.027 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t38_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 0.14/0.37  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 0.14/0.37  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.14/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.14/0.37  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.14/0.37  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.14/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.37  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.14/0.37  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.14/0.37  fof(c_0_9, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1)))), inference(assume_negation,[status(cth)],[t38_subset_1])).
% 0.14/0.37  fof(c_0_10, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))&((~r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0!=k1_subset_1(esk5_0))&(r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0=k1_subset_1(esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.14/0.37  fof(c_0_11, plain, ![X34]:k1_subset_1(X34)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.14/0.37  fof(c_0_12, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.14/0.37  fof(c_0_13, plain, ![X22, X23]:k4_xboole_0(X22,X23)=k5_xboole_0(X22,k3_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.14/0.37  cnf(c_0_14, negated_conjecture, (~r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0!=k1_subset_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_15, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.37  fof(c_0_16, plain, ![X20]:(X20=k1_xboole_0|r2_hidden(esk3_1(X20),X20)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.14/0.37  fof(c_0_17, plain, ![X25, X26]:((~r1_xboole_0(X25,X26)|k4_xboole_0(X25,X26)=X25)&(k4_xboole_0(X25,X26)!=X25|r1_xboole_0(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.14/0.37  cnf(c_0_18, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.37  cnf(c_0_20, negated_conjecture, (esk6_0!=k1_xboole_0|~r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.14/0.37  cnf(c_0_21, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.37  fof(c_0_22, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.37  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  fof(c_0_24, plain, ![X24]:r1_xboole_0(X24,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.14/0.37  cnf(c_0_25, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.37  cnf(c_0_26, negated_conjecture, (r2_hidden(esk3_1(esk6_0),esk6_0)|~r1_tarski(k1_xboole_0,k3_subset_1(esk5_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.37  cnf(c_0_27, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.37  cnf(c_0_28, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_19])).
% 0.14/0.37  cnf(c_0_29, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.37  cnf(c_0_30, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_25])).
% 0.14/0.37  cnf(c_0_31, negated_conjecture, (r2_hidden(esk1_2(k1_xboole_0,k3_subset_1(esk5_0,k1_xboole_0)),k1_xboole_0)|r2_hidden(esk3_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.14/0.37  cnf(c_0_32, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.14/0.37  fof(c_0_33, plain, ![X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(X35))|k3_subset_1(X35,X36)=k4_xboole_0(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.14/0.37  cnf(c_0_34, negated_conjecture, (r2_hidden(esk3_1(esk6_0),esk6_0)|~r2_hidden(esk1_2(k1_xboole_0,k3_subset_1(esk5_0,k1_xboole_0)),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.14/0.37  cnf(c_0_35, negated_conjecture, (r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))|esk6_0=k1_subset_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_36, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.37  cnf(c_0_37, negated_conjecture, (r2_hidden(esk3_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_34, c_0_31])).
% 0.14/0.37  cnf(c_0_38, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))), inference(rw,[status(thm)],[c_0_35, c_0_15])).
% 0.14/0.37  cnf(c_0_39, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_36, c_0_19])).
% 0.14/0.37  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_41, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.37  cnf(c_0_42, negated_conjecture, (r2_hidden(esk3_1(k1_xboole_0),k1_xboole_0)|r1_tarski(esk6_0,k3_subset_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.14/0.37  cnf(c_0_43, negated_conjecture, (~r2_hidden(esk3_1(esk6_0),k5_xboole_0(X1,k3_xboole_0(X1,esk6_0)))), inference(spm,[status(thm)],[c_0_30, c_0_37])).
% 0.14/0.37  cnf(c_0_44, negated_conjecture, (k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk6_0))=k3_subset_1(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.14/0.37  cnf(c_0_45, negated_conjecture, (r2_hidden(X1,k3_subset_1(esk5_0,esk6_0))|r2_hidden(esk3_1(k1_xboole_0),k1_xboole_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.14/0.37  cnf(c_0_46, negated_conjecture, (~r2_hidden(esk3_1(esk6_0),k3_subset_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.14/0.37  cnf(c_0_47, negated_conjecture, (r2_hidden(esk3_1(k1_xboole_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_37]), c_0_46])).
% 0.14/0.37  cnf(c_0_48, negated_conjecture, (~r2_hidden(esk3_1(k1_xboole_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_47]), c_0_32])).
% 0.14/0.37  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_47, c_0_48]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 50
% 0.14/0.37  # Proof object clause steps            : 31
% 0.14/0.37  # Proof object formula steps           : 19
% 0.14/0.37  # Proof object conjectures             : 20
% 0.14/0.37  # Proof object clause conjectures      : 17
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 12
% 0.14/0.37  # Proof object initial formulas used   : 9
% 0.14/0.37  # Proof object generating inferences   : 12
% 0.14/0.37  # Proof object simplifying inferences  : 10
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 10
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 23
% 0.14/0.37  # Removed in clause preprocessing      : 2
% 0.14/0.37  # Initial clauses in saturation        : 21
% 0.14/0.37  # Processed clauses                    : 98
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 16
% 0.14/0.37  # ...remaining for further processing  : 82
% 0.14/0.37  # Other redundant clauses eliminated   : 9
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 1
% 0.14/0.37  # Backward-rewritten                   : 9
% 0.14/0.37  # Generated clauses                    : 332
% 0.14/0.37  # ...of the previous two non-trivial   : 297
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 322
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 9
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
% 0.14/0.37  # Current number of processed clauses  : 45
% 0.14/0.37  #    Positive orientable unit clauses  : 5
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 3
% 0.14/0.37  #    Non-unit-clauses                  : 37
% 0.14/0.37  # Current number of unprocessed clauses: 241
% 0.14/0.37  # ...number of literals in the above   : 818
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 34
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 482
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 334
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 17
% 0.14/0.37  # Unit Clause-clause subsumption calls : 30
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 2
% 0.14/0.37  # BW rewrite match successes           : 2
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 5628
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.036 s
% 0.14/0.37  # System time              : 0.002 s
% 0.14/0.37  # Total time               : 0.038 s
% 0.14/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
