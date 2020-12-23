%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:14 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 123 expanded)
%              Number of clauses        :   27 (  51 expanded)
%              Number of leaves         :    7 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  150 ( 467 expanded)
%              Number of equality atoms :   40 ( 126 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t72_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,X2)
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(d4_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( ( r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          & ( ~ r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(t70_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X1,X2)
         => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t72_funct_1])).

fof(c_0_8,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_9,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | k1_relat_1(k7_relat_1(X17,X16)) = k3_xboole_0(k1_relat_1(X17),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & r2_hidden(esk2_0,esk3_0)
    & k1_funct_1(k7_relat_1(esk4_0,esk3_0),esk2_0) != k1_funct_1(esk4_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X18,X19,X20] :
      ( ( X20 != k1_funct_1(X18,X19)
        | r2_hidden(k4_tarski(X19,X20),X18)
        | ~ r2_hidden(X19,k1_relat_1(X18))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( ~ r2_hidden(k4_tarski(X19,X20),X18)
        | X20 = k1_funct_1(X18,X19)
        | ~ r2_hidden(X19,k1_relat_1(X18))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( X20 != k1_funct_1(X18,X19)
        | X20 = k1_xboole_0
        | r2_hidden(X19,k1_relat_1(X18))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( X20 != k1_xboole_0
        | X20 = k1_funct_1(X18,X19)
        | r2_hidden(X19,k1_relat_1(X18))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_15,plain,(
    ! [X23,X24,X25] :
      ( ~ v1_relat_1(X25)
      | ~ v1_funct_1(X25)
      | ~ r2_hidden(X23,k1_relat_1(k7_relat_1(X25,X24)))
      | k1_funct_1(k7_relat_1(X25,X24),X23) = k1_funct_1(X25,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t70_funct_1])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( k3_xboole_0(k1_relat_1(esk4_0),X1) = k1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_funct_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X21,X22] :
      ( ( v1_relat_1(k7_relat_1(X21,X22))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( v1_funct_1(k7_relat_1(X21,X22))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

fof(c_0_20,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | v1_relat_1(k7_relat_1(X14,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_21,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(esk4_0,X2)))
    | ~ r2_hidden(X1,k1_relat_1(esk4_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk4_0,X1),X2) = k1_funct_1(esk4_0,X2)
    | ~ r2_hidden(X2,k1_relat_1(esk4_0))
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_13])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk4_0,esk3_0),esk2_0) != k1_funct_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k1_funct_1(k7_relat_1(X1,X2),X3) = k1_xboole_0
    | r2_hidden(X3,k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k1_relat_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_23]),c_0_13])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk4_0))
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(esk4_0,X2))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk4_0,X1),X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(k7_relat_1(esk4_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_23]),c_0_13])])).

cnf(c_0_37,negated_conjecture,
    ( k1_funct_1(esk4_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk4_0,X1),X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk4_0,esk3_0),esk2_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_30,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk4_0,X1),esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:03:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.19/0.38  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.027 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t72_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,X2)=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_funct_1)).
% 0.19/0.38  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.19/0.38  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.19/0.38  fof(d4_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:((r2_hidden(X2,k1_relat_1(X1))=>(X3=k1_funct_1(X1,X2)<=>r2_hidden(k4_tarski(X2,X3),X1)))&(~(r2_hidden(X2,k1_relat_1(X1)))=>(X3=k1_funct_1(X1,X2)<=>X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 0.19/0.38  fof(t70_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_funct_1)).
% 0.19/0.38  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.19/0.38  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.19/0.38  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,X2)=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1)))), inference(assume_negation,[status(cth)],[t72_funct_1])).
% 0.19/0.38  fof(c_0_8, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.19/0.38  fof(c_0_9, plain, ![X16, X17]:(~v1_relat_1(X17)|k1_relat_1(k7_relat_1(X17,X16))=k3_xboole_0(k1_relat_1(X17),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.19/0.38  fof(c_0_10, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&(r2_hidden(esk2_0,esk3_0)&k1_funct_1(k7_relat_1(esk4_0,esk3_0),esk2_0)!=k1_funct_1(esk4_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.19/0.38  cnf(c_0_11, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  cnf(c_0_12, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  fof(c_0_14, plain, ![X18, X19, X20]:(((X20!=k1_funct_1(X18,X19)|r2_hidden(k4_tarski(X19,X20),X18)|~r2_hidden(X19,k1_relat_1(X18))|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(~r2_hidden(k4_tarski(X19,X20),X18)|X20=k1_funct_1(X18,X19)|~r2_hidden(X19,k1_relat_1(X18))|(~v1_relat_1(X18)|~v1_funct_1(X18))))&((X20!=k1_funct_1(X18,X19)|X20=k1_xboole_0|r2_hidden(X19,k1_relat_1(X18))|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(X20!=k1_xboole_0|X20=k1_funct_1(X18,X19)|r2_hidden(X19,k1_relat_1(X18))|(~v1_relat_1(X18)|~v1_funct_1(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).
% 0.19/0.38  fof(c_0_15, plain, ![X23, X24, X25]:(~v1_relat_1(X25)|~v1_funct_1(X25)|(~r2_hidden(X23,k1_relat_1(k7_relat_1(X25,X24)))|k1_funct_1(k7_relat_1(X25,X24),X23)=k1_funct_1(X25,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t70_funct_1])])).
% 0.19/0.38  cnf(c_0_16, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (k3_xboole_0(k1_relat_1(esk4_0),X1)=k1_relat_1(k7_relat_1(esk4_0,X1))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.38  cnf(c_0_18, plain, (X1=k1_xboole_0|r2_hidden(X3,k1_relat_1(X2))|X1!=k1_funct_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  fof(c_0_19, plain, ![X21, X22]:((v1_relat_1(k7_relat_1(X21,X22))|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(v1_funct_1(k7_relat_1(X21,X22))|(~v1_relat_1(X21)|~v1_funct_1(X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.19/0.38  fof(c_0_20, plain, ![X14, X15]:(~v1_relat_1(X14)|v1_relat_1(k7_relat_1(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.19/0.38  cnf(c_0_21, plain, (k1_funct_1(k7_relat_1(X1,X3),X2)=k1_funct_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(k7_relat_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (r2_hidden(X1,k1_relat_1(k7_relat_1(esk4_0,X2)))|~r2_hidden(X1,k1_relat_1(esk4_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_24, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  cnf(c_0_25, plain, (k1_funct_1(X1,X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_26, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_27, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (k1_funct_1(k7_relat_1(esk4_0,X1),X2)=k1_funct_1(esk4_0,X2)|~r2_hidden(X2,k1_relat_1(esk4_0))|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_13])])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (r2_hidden(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (k1_funct_1(k7_relat_1(esk4_0,esk3_0),esk2_0)!=k1_funct_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_31, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_32, plain, (k1_funct_1(k7_relat_1(X1,X2),X3)=k1_xboole_0|r2_hidden(X3,k1_relat_1(k7_relat_1(X1,X2)))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (~r2_hidden(esk2_0,k1_relat_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (k1_funct_1(esk4_0,X1)=k1_xboole_0|r2_hidden(X1,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_23]), c_0_13])])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk4_0))|~r2_hidden(X1,k1_relat_1(k7_relat_1(esk4_0,X2)))), inference(spm,[status(thm)],[c_0_31, c_0_17])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (k1_funct_1(k7_relat_1(esk4_0,X1),X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(k7_relat_1(esk4_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_23]), c_0_13])])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (k1_funct_1(esk4_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (k1_funct_1(k7_relat_1(esk4_0,X1),X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (k1_funct_1(k7_relat_1(esk4_0,esk3_0),esk2_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_30, c_0_37])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (k1_funct_1(k7_relat_1(esk4_0,X1),esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_38])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 42
% 0.19/0.38  # Proof object clause steps            : 27
% 0.19/0.38  # Proof object formula steps           : 15
% 0.19/0.38  # Proof object conjectures             : 19
% 0.19/0.38  # Proof object clause conjectures      : 16
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 11
% 0.19/0.38  # Proof object initial formulas used   : 7
% 0.19/0.38  # Proof object generating inferences   : 11
% 0.19/0.38  # Proof object simplifying inferences  : 15
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 7
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 19
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 19
% 0.19/0.38  # Processed clauses                    : 79
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 7
% 0.19/0.38  # ...remaining for further processing  : 72
% 0.19/0.38  # Other redundant clauses eliminated   : 6
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 3
% 0.19/0.38  # Generated clauses                    : 203
% 0.19/0.38  # ...of the previous two non-trivial   : 185
% 0.19/0.38  # Contextual simplify-reflections      : 4
% 0.19/0.38  # Paramodulations                      : 193
% 0.19/0.38  # Factorizations                       : 4
% 0.19/0.38  # Equation resolutions                 : 6
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 46
% 0.19/0.38  #    Positive orientable unit clauses  : 10
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 35
% 0.19/0.38  # Current number of unprocessed clauses: 142
% 0.19/0.38  # ...number of literals in the above   : 470
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 20
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 131
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 89
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 10
% 0.19/0.38  # Unit Clause-clause subsumption calls : 32
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 15
% 0.19/0.38  # BW rewrite match successes           : 3
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 4908
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.032 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.037 s
% 0.19/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
