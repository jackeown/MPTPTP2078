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
% DateTime   : Thu Dec  3 10:56:57 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   34 (  73 expanded)
%              Number of clauses        :   21 (  27 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  196 ( 477 expanded)
%              Number of equality atoms :   32 (  65 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( v2_wellord1(X3)
          & r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3))
          & ! [X4] :
              ( r2_hidden(X4,k1_wellord1(X3,X1))
             => ( r2_hidden(k4_tarski(X4,X2),X3)
                & X4 != X2 ) ) )
       => r2_hidden(k4_tarski(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_wellord1)).

fof(l4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
      <=> ! [X2,X3] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r2_hidden(X3,k3_relat_1(X1))
              & X2 != X3
              & ~ r2_hidden(k4_tarski(X2,X3),X1)
              & ~ r2_hidden(k4_tarski(X3,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t37_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( v2_wellord1(X3)
          & r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) )
       => ( r2_hidden(k4_tarski(X1,X2),X3)
        <=> r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( ( v2_wellord1(X3)
            & r2_hidden(X1,k3_relat_1(X3))
            & r2_hidden(X2,k3_relat_1(X3))
            & ! [X4] :
                ( r2_hidden(X4,k1_wellord1(X3,X1))
               => ( r2_hidden(k4_tarski(X4,X2),X3)
                  & X4 != X2 ) ) )
         => r2_hidden(k4_tarski(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t42_wellord1])).

fof(c_0_7,plain,(
    ! [X16,X17,X18] :
      ( ( ~ v6_relat_2(X16)
        | ~ r2_hidden(X17,k3_relat_1(X16))
        | ~ r2_hidden(X18,k3_relat_1(X16))
        | X17 = X18
        | r2_hidden(k4_tarski(X17,X18),X16)
        | r2_hidden(k4_tarski(X18,X17),X16)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk2_1(X16),k3_relat_1(X16))
        | v6_relat_2(X16)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk3_1(X16),k3_relat_1(X16))
        | v6_relat_2(X16)
        | ~ v1_relat_1(X16) )
      & ( esk2_1(X16) != esk3_1(X16)
        | v6_relat_2(X16)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(esk2_1(X16),esk3_1(X16)),X16)
        | v6_relat_2(X16)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(esk3_1(X16),esk2_1(X16)),X16)
        | v6_relat_2(X16)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).

fof(c_0_8,negated_conjecture,(
    ! [X27] :
      ( v1_relat_1(esk6_0)
      & v2_wellord1(esk6_0)
      & r2_hidden(esk4_0,k3_relat_1(esk6_0))
      & r2_hidden(esk5_0,k3_relat_1(esk6_0))
      & ( r2_hidden(k4_tarski(X27,esk5_0),esk6_0)
        | ~ r2_hidden(X27,k1_wellord1(esk6_0,esk4_0)) )
      & ( X27 != esk5_0
        | ~ r2_hidden(X27,k1_wellord1(esk6_0,esk4_0)) )
      & ~ r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

cnf(c_0_9,plain,
    ( X2 = X3
    | r2_hidden(k4_tarski(X2,X3),X1)
    | r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk5_0,k3_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X15] :
      ( ( v1_relat_2(X15)
        | ~ v2_wellord1(X15)
        | ~ v1_relat_1(X15) )
      & ( v8_relat_2(X15)
        | ~ v2_wellord1(X15)
        | ~ v1_relat_1(X15) )
      & ( v4_relat_2(X15)
        | ~ v2_wellord1(X15)
        | ~ v1_relat_1(X15) )
      & ( v6_relat_2(X15)
        | ~ v2_wellord1(X15)
        | ~ v1_relat_1(X15) )
      & ( v1_wellord1(X15)
        | ~ v2_wellord1(X15)
        | ~ v1_relat_1(X15) )
      & ( ~ v1_relat_2(X15)
        | ~ v8_relat_2(X15)
        | ~ v4_relat_2(X15)
        | ~ v6_relat_2(X15)
        | ~ v1_wellord1(X15)
        | v2_wellord1(X15)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_13,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13] :
      ( ( X10 != X8
        | ~ r2_hidden(X10,X9)
        | X9 != k1_wellord1(X7,X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(X10,X8),X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k1_wellord1(X7,X8)
        | ~ v1_relat_1(X7) )
      & ( X11 = X8
        | ~ r2_hidden(k4_tarski(X11,X8),X7)
        | r2_hidden(X11,X9)
        | X9 != k1_wellord1(X7,X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(esk1_3(X7,X12,X13),X13)
        | esk1_3(X7,X12,X13) = X12
        | ~ r2_hidden(k4_tarski(esk1_3(X7,X12,X13),X12),X7)
        | X13 = k1_wellord1(X7,X12)
        | ~ v1_relat_1(X7) )
      & ( esk1_3(X7,X12,X13) != X12
        | r2_hidden(esk1_3(X7,X12,X13),X13)
        | X13 = k1_wellord1(X7,X12)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(esk1_3(X7,X12,X13),X12),X7)
        | r2_hidden(esk1_3(X7,X12,X13),X13)
        | X13 = k1_wellord1(X7,X12)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

cnf(c_0_14,negated_conjecture,
    ( X1 = esk5_0
    | r2_hidden(k4_tarski(esk5_0,X1),esk6_0)
    | r2_hidden(k4_tarski(X1,esk5_0),esk6_0)
    | ~ v6_relat_2(esk6_0)
    | ~ r2_hidden(X1,k3_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_15,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v2_wellord1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( X1 = esk5_0
    | r2_hidden(k4_tarski(X1,esk5_0),esk6_0)
    | r2_hidden(k4_tarski(esk5_0,X1),esk6_0)
    | ~ r2_hidden(X1,k3_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_11])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk4_0,k3_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( X1 != esk5_0
    | ~ r2_hidden(X1,k1_wellord1(esk6_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_22,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_23,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( esk5_0 = esk4_0
    | r2_hidden(k4_tarski(esk5_0,esk4_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k1_wellord1(esk6_0,esk4_0)) ),
    inference(er,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X21,X22,X23] :
      ( ( ~ r2_hidden(k4_tarski(X21,X22),X23)
        | r1_tarski(k1_wellord1(X23,X21),k1_wellord1(X23,X22))
        | ~ v2_wellord1(X23)
        | ~ r2_hidden(X21,k3_relat_1(X23))
        | ~ r2_hidden(X22,k3_relat_1(X23))
        | ~ v1_relat_1(X23) )
      & ( ~ r1_tarski(k1_wellord1(X23,X21),k1_wellord1(X23,X22))
        | r2_hidden(k4_tarski(X21,X22),X23)
        | ~ v2_wellord1(X23)
        | ~ r2_hidden(X21,k3_relat_1(X23))
        | ~ r2_hidden(X22,k3_relat_1(X23))
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_wellord1])])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( esk5_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_11])]),c_0_25])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r1_tarski(k1_wellord1(X1,X2),k1_wellord1(X1,X3))
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk4_0,esk4_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_20,c_0_28])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(X1,X1),X2)
    | ~ v2_wellord1(X2)
    | ~ r2_hidden(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_16]),c_0_19]),c_0_11])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:23:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.13/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t42_wellord1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>((((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))&![X4]:(r2_hidden(X4,k1_wellord1(X3,X1))=>(r2_hidden(k4_tarski(X4,X2),X3)&X4!=X2)))=>r2_hidden(k4_tarski(X1,X2),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_wellord1)).
% 0.13/0.37  fof(l4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v6_relat_2(X1)<=>![X2, X3]:~(((((r2_hidden(X2,k3_relat_1(X1))&r2_hidden(X3,k3_relat_1(X1)))&X2!=X3)&~(r2_hidden(k4_tarski(X2,X3),X1)))&~(r2_hidden(k4_tarski(X3,X2),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l4_wellord1)).
% 0.13/0.37  fof(d4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)<=>((((v1_relat_2(X1)&v8_relat_2(X1))&v4_relat_2(X1))&v6_relat_2(X1))&v1_wellord1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_wellord1)).
% 0.13/0.37  fof(d1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k1_wellord1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4!=X2&r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 0.13/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.37  fof(t37_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_wellord1)).
% 0.13/0.37  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>((((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))&![X4]:(r2_hidden(X4,k1_wellord1(X3,X1))=>(r2_hidden(k4_tarski(X4,X2),X3)&X4!=X2)))=>r2_hidden(k4_tarski(X1,X2),X3)))), inference(assume_negation,[status(cth)],[t42_wellord1])).
% 0.13/0.37  fof(c_0_7, plain, ![X16, X17, X18]:((~v6_relat_2(X16)|(~r2_hidden(X17,k3_relat_1(X16))|~r2_hidden(X18,k3_relat_1(X16))|X17=X18|r2_hidden(k4_tarski(X17,X18),X16)|r2_hidden(k4_tarski(X18,X17),X16))|~v1_relat_1(X16))&(((((r2_hidden(esk2_1(X16),k3_relat_1(X16))|v6_relat_2(X16)|~v1_relat_1(X16))&(r2_hidden(esk3_1(X16),k3_relat_1(X16))|v6_relat_2(X16)|~v1_relat_1(X16)))&(esk2_1(X16)!=esk3_1(X16)|v6_relat_2(X16)|~v1_relat_1(X16)))&(~r2_hidden(k4_tarski(esk2_1(X16),esk3_1(X16)),X16)|v6_relat_2(X16)|~v1_relat_1(X16)))&(~r2_hidden(k4_tarski(esk3_1(X16),esk2_1(X16)),X16)|v6_relat_2(X16)|~v1_relat_1(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).
% 0.13/0.37  fof(c_0_8, negated_conjecture, ![X27]:(v1_relat_1(esk6_0)&((((v2_wellord1(esk6_0)&r2_hidden(esk4_0,k3_relat_1(esk6_0)))&r2_hidden(esk5_0,k3_relat_1(esk6_0)))&((r2_hidden(k4_tarski(X27,esk5_0),esk6_0)|~r2_hidden(X27,k1_wellord1(esk6_0,esk4_0)))&(X27!=esk5_0|~r2_hidden(X27,k1_wellord1(esk6_0,esk4_0)))))&~r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).
% 0.13/0.37  cnf(c_0_9, plain, (X2=X3|r2_hidden(k4_tarski(X2,X3),X1)|r2_hidden(k4_tarski(X3,X2),X1)|~v6_relat_2(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r2_hidden(X3,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_10, negated_conjecture, (r2_hidden(esk5_0,k3_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_11, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  fof(c_0_12, plain, ![X15]:((((((v1_relat_2(X15)|~v2_wellord1(X15)|~v1_relat_1(X15))&(v8_relat_2(X15)|~v2_wellord1(X15)|~v1_relat_1(X15)))&(v4_relat_2(X15)|~v2_wellord1(X15)|~v1_relat_1(X15)))&(v6_relat_2(X15)|~v2_wellord1(X15)|~v1_relat_1(X15)))&(v1_wellord1(X15)|~v2_wellord1(X15)|~v1_relat_1(X15)))&(~v1_relat_2(X15)|~v8_relat_2(X15)|~v4_relat_2(X15)|~v6_relat_2(X15)|~v1_wellord1(X15)|v2_wellord1(X15)|~v1_relat_1(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).
% 0.13/0.37  fof(c_0_13, plain, ![X7, X8, X9, X10, X11, X12, X13]:((((X10!=X8|~r2_hidden(X10,X9)|X9!=k1_wellord1(X7,X8)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(X10,X8),X7)|~r2_hidden(X10,X9)|X9!=k1_wellord1(X7,X8)|~v1_relat_1(X7)))&(X11=X8|~r2_hidden(k4_tarski(X11,X8),X7)|r2_hidden(X11,X9)|X9!=k1_wellord1(X7,X8)|~v1_relat_1(X7)))&((~r2_hidden(esk1_3(X7,X12,X13),X13)|(esk1_3(X7,X12,X13)=X12|~r2_hidden(k4_tarski(esk1_3(X7,X12,X13),X12),X7))|X13=k1_wellord1(X7,X12)|~v1_relat_1(X7))&((esk1_3(X7,X12,X13)!=X12|r2_hidden(esk1_3(X7,X12,X13),X13)|X13=k1_wellord1(X7,X12)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(esk1_3(X7,X12,X13),X12),X7)|r2_hidden(esk1_3(X7,X12,X13),X13)|X13=k1_wellord1(X7,X12)|~v1_relat_1(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).
% 0.13/0.37  cnf(c_0_14, negated_conjecture, (X1=esk5_0|r2_hidden(k4_tarski(esk5_0,X1),esk6_0)|r2_hidden(k4_tarski(X1,esk5_0),esk6_0)|~v6_relat_2(esk6_0)|~r2_hidden(X1,k3_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11])])).
% 0.13/0.37  cnf(c_0_15, plain, (v6_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (v2_wellord1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_17, plain, (X1=X2|r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (X1=esk5_0|r2_hidden(k4_tarski(X1,esk5_0),esk6_0)|r2_hidden(k4_tarski(esk5_0,X1),esk6_0)|~r2_hidden(X1,k3_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_11])])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (r2_hidden(esk4_0,k3_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (~r2_hidden(k4_tarski(esk4_0,esk5_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (X1!=esk5_0|~r2_hidden(X1,k1_wellord1(esk6_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  fof(c_0_22, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.37  cnf(c_0_23, plain, (X1=X2|r2_hidden(X1,k1_wellord1(X3,X2))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(er,[status(thm)],[c_0_17])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (esk5_0=esk4_0|r2_hidden(k4_tarski(esk5_0,esk4_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (~r2_hidden(esk5_0,k1_wellord1(esk6_0,esk4_0))), inference(er,[status(thm)],[c_0_21])).
% 0.13/0.37  fof(c_0_26, plain, ![X21, X22, X23]:((~r2_hidden(k4_tarski(X21,X22),X23)|r1_tarski(k1_wellord1(X23,X21),k1_wellord1(X23,X22))|(~v2_wellord1(X23)|~r2_hidden(X21,k3_relat_1(X23))|~r2_hidden(X22,k3_relat_1(X23)))|~v1_relat_1(X23))&(~r1_tarski(k1_wellord1(X23,X21),k1_wellord1(X23,X22))|r2_hidden(k4_tarski(X21,X22),X23)|(~v2_wellord1(X23)|~r2_hidden(X21,k3_relat_1(X23))|~r2_hidden(X22,k3_relat_1(X23)))|~v1_relat_1(X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_wellord1])])])).
% 0.13/0.37  cnf(c_0_27, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (esk5_0=esk4_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_11])]), c_0_25])).
% 0.13/0.37  cnf(c_0_29, plain, (r2_hidden(k4_tarski(X2,X3),X1)|~r1_tarski(k1_wellord1(X1,X2),k1_wellord1(X1,X3))|~v2_wellord1(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r2_hidden(X3,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.37  cnf(c_0_30, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_27])).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, (~r2_hidden(k4_tarski(esk4_0,esk4_0),esk6_0)), inference(rw,[status(thm)],[c_0_20, c_0_28])).
% 0.13/0.37  cnf(c_0_32, plain, (r2_hidden(k4_tarski(X1,X1),X2)|~v2_wellord1(X2)|~r2_hidden(X1,k3_relat_1(X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_16]), c_0_19]), c_0_11])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 34
% 0.13/0.37  # Proof object clause steps            : 21
% 0.13/0.37  # Proof object formula steps           : 13
% 0.13/0.37  # Proof object conjectures             : 16
% 0.13/0.37  # Proof object clause conjectures      : 13
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 11
% 0.13/0.37  # Proof object initial formulas used   : 6
% 0.13/0.37  # Proof object generating inferences   : 6
% 0.13/0.37  # Proof object simplifying inferences  : 17
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 6
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 30
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 30
% 0.13/0.37  # Processed clauses                    : 68
% 0.13/0.37  # ...of these trivial                  : 1
% 0.13/0.37  # ...subsumed                          : 6
% 0.13/0.37  # ...remaining for further processing  : 61
% 0.13/0.37  # Other redundant clauses eliminated   : 7
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 1
% 0.13/0.37  # Backward-rewritten                   : 8
% 0.13/0.37  # Generated clauses                    : 63
% 0.13/0.37  # ...of the previous two non-trivial   : 61
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 57
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 7
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
% 0.13/0.37  # Current number of processed clauses  : 46
% 0.13/0.37  #    Positive orientable unit clauses  : 5
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 39
% 0.13/0.37  # Current number of unprocessed clauses: 15
% 0.13/0.37  # ...number of literals in the above   : 84
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 9
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 273
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 60
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.13/0.37  # Unit Clause-clause subsumption calls : 31
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 5
% 0.13/0.37  # BW rewrite match successes           : 1
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 3716
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.031 s
% 0.13/0.37  # System time              : 0.005 s
% 0.13/0.37  # Total time               : 0.036 s
% 0.13/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
