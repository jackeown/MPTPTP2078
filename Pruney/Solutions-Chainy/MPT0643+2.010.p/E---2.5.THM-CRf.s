%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:42 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 119 expanded)
%              Number of clauses        :   22 (  37 expanded)
%              Number of leaves         :    5 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  183 ( 913 expanded)
%              Number of equality atoms :   52 ( 345 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   23 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( ( k1_relat_1(X2) = X1
              & k1_relat_1(X3) = X1
              & r1_tarski(k2_relat_1(X3),X1)
              & v2_funct_1(X2)
              & k5_relat_1(X3,X2) = X2 )
           => X3 = k6_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).

fof(t21_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
          <=> ( r2_hidden(X1,k1_relat_1(X3))
              & r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(t22_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
           => k1_funct_1(k5_relat_1(X3,X2),X1) = k1_funct_1(X2,k1_funct_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

fof(t34_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( X2 = k6_relat_1(X1)
      <=> ( k1_relat_1(X2) = X1
          & ! [X3] :
              ( r2_hidden(X3,X1)
             => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ( ( k1_relat_1(X2) = X1
                & k1_relat_1(X3) = X1
                & r1_tarski(k2_relat_1(X3),X1)
                & v2_funct_1(X2)
                & k5_relat_1(X3,X2) = X2 )
             => X3 = k6_relat_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_funct_1])).

fof(c_0_6,plain,(
    ! [X9,X10,X11] :
      ( ( r2_hidden(X9,k1_relat_1(X11))
        | ~ r2_hidden(X9,k1_relat_1(k5_relat_1(X11,X10)))
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(k1_funct_1(X11,X9),k1_relat_1(X10))
        | ~ r2_hidden(X9,k1_relat_1(k5_relat_1(X11,X10)))
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( ~ r2_hidden(X9,k1_relat_1(X11))
        | ~ r2_hidden(k1_funct_1(X11,X9),k1_relat_1(X10))
        | r2_hidden(X9,k1_relat_1(k5_relat_1(X11,X10)))
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & k1_relat_1(esk5_0) = esk4_0
    & k1_relat_1(esk6_0) = esk4_0
    & r1_tarski(k2_relat_1(esk6_0),esk4_0)
    & v2_funct_1(esk5_0)
    & k5_relat_1(esk6_0,esk5_0) = esk5_0
    & esk6_0 != k6_relat_1(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v2_funct_1(X4)
        | ~ r2_hidden(X5,k1_relat_1(X4))
        | ~ r2_hidden(X6,k1_relat_1(X4))
        | k1_funct_1(X4,X5) != k1_funct_1(X4,X6)
        | X5 = X6
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4) )
      & ( r2_hidden(esk1_1(X4),k1_relat_1(X4))
        | v2_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4) )
      & ( r2_hidden(esk2_1(X4),k1_relat_1(X4))
        | v2_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4) )
      & ( k1_funct_1(X4,esk1_1(X4)) = k1_funct_1(X4,esk2_1(X4))
        | v2_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4) )
      & ( esk1_1(X4) != esk2_1(X4)
        | v2_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

fof(c_0_9,plain,(
    ! [X12,X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ v1_funct_1(X13)
      | ~ v1_relat_1(X14)
      | ~ v1_funct_1(X14)
      | ~ r2_hidden(X12,k1_relat_1(k5_relat_1(X14,X13)))
      | k1_funct_1(k5_relat_1(X14,X13),X12) = k1_funct_1(X13,k1_funct_1(X14,X12)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).

cnf(c_0_10,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k1_relat_1(X3))
    | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( k1_funct_1(k5_relat_1(X2,X1),X3) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( k5_relat_1(esk6_0,esk5_0) = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k1_funct_1(X1,X2),esk4_0)
    | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,esk5_0)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])])).

cnf(c_0_21,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(esk5_0,X1) != k1_funct_1(esk5_0,X2)
    | ~ r2_hidden(X2,esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_11]),c_0_15]),c_0_12]),c_0_13])])).

cnf(c_0_22,negated_conjecture,
    ( k1_funct_1(esk5_0,k1_funct_1(esk6_0,X1)) = k1_funct_1(esk5_0,X1)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_11]),c_0_18]),c_0_12]),c_0_19]),c_0_13])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,X1),esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_17]),c_0_11]),c_0_18]),c_0_19])])).

fof(c_0_24,plain,(
    ! [X15,X16,X17] :
      ( ( k1_relat_1(X16) = X15
        | X16 != k6_relat_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(X17,X15)
        | k1_funct_1(X16,X17) = X17
        | X16 != k6_relat_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( r2_hidden(esk3_2(X15,X16),X15)
        | k1_relat_1(X16) != X15
        | X16 = k6_relat_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( k1_funct_1(X16,esk3_2(X15,X16)) != esk3_2(X15,X16)
        | k1_relat_1(X16) != X15
        | X16 = k6_relat_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).

cnf(c_0_25,negated_conjecture,
    ( X1 = k1_funct_1(esk6_0,X2)
    | k1_funct_1(esk5_0,X1) != k1_funct_1(esk5_0,X2)
    | ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X2,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_26,plain,
    ( X1 = k6_relat_1(X2)
    | k1_funct_1(X1,esk3_2(X2,X1)) != esk3_2(X2,X1)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = X1
    | ~ r2_hidden(X1,esk4_0) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,negated_conjecture,
    ( k6_relat_1(X1) = esk6_0
    | esk4_0 != X1
    | ~ r2_hidden(esk3_2(X1,esk6_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_18]),c_0_19])])).

cnf(c_0_30,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | X2 = k6_relat_1(X1)
    | k1_relat_1(X2) != X1
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( esk6_0 != k6_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_28]),c_0_18]),c_0_19])]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_AE_CS_SP_PI_S0Y
% 0.20/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t50_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)&r1_tarski(k2_relat_1(X3),X1))&v2_funct_1(X2))&k5_relat_1(X3,X2)=X2)=>X3=k6_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_1)).
% 0.20/0.38  fof(t21_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 0.20/0.38  fof(d8_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2, X3]:(((r2_hidden(X2,k1_relat_1(X1))&r2_hidden(X3,k1_relat_1(X1)))&k1_funct_1(X1,X2)=k1_funct_1(X1,X3))=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 0.20/0.38  fof(t22_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))=>k1_funct_1(k5_relat_1(X3,X2),X1)=k1_funct_1(X2,k1_funct_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 0.20/0.38  fof(t34_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k6_relat_1(X1)<=>(k1_relat_1(X2)=X1&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 0.20/0.38  fof(c_0_5, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)&r1_tarski(k2_relat_1(X3),X1))&v2_funct_1(X2))&k5_relat_1(X3,X2)=X2)=>X3=k6_relat_1(X1))))), inference(assume_negation,[status(cth)],[t50_funct_1])).
% 0.20/0.38  fof(c_0_6, plain, ![X9, X10, X11]:(((r2_hidden(X9,k1_relat_1(X11))|~r2_hidden(X9,k1_relat_1(k5_relat_1(X11,X10)))|(~v1_relat_1(X11)|~v1_funct_1(X11))|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(r2_hidden(k1_funct_1(X11,X9),k1_relat_1(X10))|~r2_hidden(X9,k1_relat_1(k5_relat_1(X11,X10)))|(~v1_relat_1(X11)|~v1_funct_1(X11))|(~v1_relat_1(X10)|~v1_funct_1(X10))))&(~r2_hidden(X9,k1_relat_1(X11))|~r2_hidden(k1_funct_1(X11,X9),k1_relat_1(X10))|r2_hidden(X9,k1_relat_1(k5_relat_1(X11,X10)))|(~v1_relat_1(X11)|~v1_funct_1(X11))|(~v1_relat_1(X10)|~v1_funct_1(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).
% 0.20/0.38  fof(c_0_7, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&(((((k1_relat_1(esk5_0)=esk4_0&k1_relat_1(esk6_0)=esk4_0)&r1_tarski(k2_relat_1(esk6_0),esk4_0))&v2_funct_1(esk5_0))&k5_relat_1(esk6_0,esk5_0)=esk5_0)&esk6_0!=k6_relat_1(esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.20/0.38  fof(c_0_8, plain, ![X4, X5, X6]:((~v2_funct_1(X4)|(~r2_hidden(X5,k1_relat_1(X4))|~r2_hidden(X6,k1_relat_1(X4))|k1_funct_1(X4,X5)!=k1_funct_1(X4,X6)|X5=X6)|(~v1_relat_1(X4)|~v1_funct_1(X4)))&((((r2_hidden(esk1_1(X4),k1_relat_1(X4))|v2_funct_1(X4)|(~v1_relat_1(X4)|~v1_funct_1(X4)))&(r2_hidden(esk2_1(X4),k1_relat_1(X4))|v2_funct_1(X4)|(~v1_relat_1(X4)|~v1_funct_1(X4))))&(k1_funct_1(X4,esk1_1(X4))=k1_funct_1(X4,esk2_1(X4))|v2_funct_1(X4)|(~v1_relat_1(X4)|~v1_funct_1(X4))))&(esk1_1(X4)!=esk2_1(X4)|v2_funct_1(X4)|(~v1_relat_1(X4)|~v1_funct_1(X4))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).
% 0.20/0.38  fof(c_0_9, plain, ![X12, X13, X14]:(~v1_relat_1(X13)|~v1_funct_1(X13)|(~v1_relat_1(X14)|~v1_funct_1(X14)|(~r2_hidden(X12,k1_relat_1(k5_relat_1(X14,X13)))|k1_funct_1(k5_relat_1(X14,X13),X12)=k1_funct_1(X13,k1_funct_1(X14,X12))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).
% 0.20/0.38  cnf(c_0_10, plain, (r2_hidden(k1_funct_1(X1,X2),k1_relat_1(X3))|~r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X3)))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_11, negated_conjecture, (k1_relat_1(esk5_0)=esk4_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_12, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_14, plain, (X2=X3|~v2_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X3,k1_relat_1(X1))|k1_funct_1(X1,X2)!=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_15, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_16, plain, (k1_funct_1(k5_relat_1(X2,X1),X3)=k1_funct_1(X1,k1_funct_1(X2,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_17, negated_conjecture, (k5_relat_1(esk6_0,esk5_0)=esk5_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_18, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (r2_hidden(k1_funct_1(X1,X2),esk4_0)|~r2_hidden(X2,k1_relat_1(k5_relat_1(X1,esk5_0)))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), c_0_13])])).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (X1=X2|k1_funct_1(esk5_0,X1)!=k1_funct_1(esk5_0,X2)|~r2_hidden(X2,esk4_0)|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_11]), c_0_15]), c_0_12]), c_0_13])])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (k1_funct_1(esk5_0,k1_funct_1(esk6_0,X1))=k1_funct_1(esk5_0,X1)|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_11]), c_0_18]), c_0_12]), c_0_19]), c_0_13])])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,X1),esk4_0)|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_17]), c_0_11]), c_0_18]), c_0_19])])).
% 0.20/0.38  fof(c_0_24, plain, ![X15, X16, X17]:(((k1_relat_1(X16)=X15|X16!=k6_relat_1(X15)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(~r2_hidden(X17,X15)|k1_funct_1(X16,X17)=X17|X16!=k6_relat_1(X15)|(~v1_relat_1(X16)|~v1_funct_1(X16))))&((r2_hidden(esk3_2(X15,X16),X15)|k1_relat_1(X16)!=X15|X16=k6_relat_1(X15)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(k1_funct_1(X16,esk3_2(X15,X16))!=esk3_2(X15,X16)|k1_relat_1(X16)!=X15|X16=k6_relat_1(X15)|(~v1_relat_1(X16)|~v1_funct_1(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (X1=k1_funct_1(esk6_0,X2)|k1_funct_1(esk5_0,X1)!=k1_funct_1(esk5_0,X2)|~r2_hidden(X1,esk4_0)|~r2_hidden(X2,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.20/0.38  cnf(c_0_26, plain, (X1=k6_relat_1(X2)|k1_funct_1(X1,esk3_2(X2,X1))!=esk3_2(X2,X1)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (k1_funct_1(esk6_0,X1)=X1|~r2_hidden(X1,esk4_0)), inference(er,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (k6_relat_1(X1)=esk6_0|esk4_0!=X1|~r2_hidden(esk3_2(X1,esk6_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_18]), c_0_19])])).
% 0.20/0.38  cnf(c_0_30, plain, (r2_hidden(esk3_2(X1,X2),X1)|X2=k6_relat_1(X1)|k1_relat_1(X2)!=X1|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (esk6_0!=k6_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_28]), c_0_18]), c_0_19])]), c_0_31]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 33
% 0.20/0.38  # Proof object clause steps            : 22
% 0.20/0.38  # Proof object formula steps           : 11
% 0.20/0.38  # Proof object conjectures             : 20
% 0.20/0.38  # Proof object clause conjectures      : 17
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 14
% 0.20/0.38  # Proof object initial formulas used   : 5
% 0.20/0.38  # Proof object generating inferences   : 8
% 0.20/0.38  # Proof object simplifying inferences  : 27
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 5
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 23
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 23
% 0.20/0.38  # Processed clauses                    : 46
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 4
% 0.20/0.38  # ...remaining for further processing  : 42
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 0
% 0.20/0.38  # Generated clauses                    : 115
% 0.20/0.38  # ...of the previous two non-trivial   : 86
% 0.20/0.38  # Contextual simplify-reflections      : 4
% 0.20/0.38  # Paramodulations                      : 111
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 4
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 42
% 0.20/0.38  #    Positive orientable unit clauses  : 9
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 32
% 0.20/0.38  # Current number of unprocessed clauses: 63
% 0.20/0.38  # ...number of literals in the above   : 471
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 0
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 190
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 25
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 6
% 0.20/0.38  # Unit Clause-clause subsumption calls : 0
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 0
% 0.20/0.38  # BW rewrite match successes           : 0
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 4463
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.029 s
% 0.20/0.38  # System time              : 0.007 s
% 0.20/0.38  # Total time               : 0.035 s
% 0.20/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
