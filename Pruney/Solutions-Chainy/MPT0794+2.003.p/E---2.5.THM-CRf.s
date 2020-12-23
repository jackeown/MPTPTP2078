%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:58 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 215 expanded)
%              Number of clauses        :   24 (  65 expanded)
%              Number of leaves         :    3 (  53 expanded)
%              Depth                    :    7
%              Number of atoms          :  214 (2058 expanded)
%              Number of equality atoms :   29 ( 366 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   90 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( r3_wellord1(X1,X2,X3)
               => ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X1)
                   => ( X4 = X5
                      | ( r2_hidden(k4_tarski(k1_funct_1(X3,X4),k1_funct_1(X3,X5)),X2)
                        & k1_funct_1(X3,X4) != k1_funct_1(X3,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_wellord1)).

fof(d7_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( r3_wellord1(X1,X2,X3)
              <=> ( k1_relat_1(X3) = k3_relat_1(X1)
                  & k2_relat_1(X3) = k3_relat_1(X2)
                  & v2_funct_1(X3)
                  & ! [X4,X5] :
                      ( r2_hidden(k4_tarski(X4,X5),X1)
                    <=> ( r2_hidden(X4,k3_relat_1(X1))
                        & r2_hidden(X5,k3_relat_1(X1))
                        & r2_hidden(k4_tarski(k1_funct_1(X3,X4),k1_funct_1(X3,X5)),X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_wellord1)).

fof(t56_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k1_relat_1(X2)) )
       => ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
          & X1 = k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( ( v1_relat_1(X3)
                  & v1_funct_1(X3) )
               => ( r3_wellord1(X1,X2,X3)
                 => ! [X4,X5] :
                      ( r2_hidden(k4_tarski(X4,X5),X1)
                     => ( X4 = X5
                        | ( r2_hidden(k4_tarski(k1_funct_1(X3,X4),k1_funct_1(X3,X5)),X2)
                          & k1_funct_1(X3,X4) != k1_funct_1(X3,X5) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t45_wellord1])).

fof(c_0_4,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14] :
      ( ( k1_relat_1(X10) = k3_relat_1(X8)
        | ~ r3_wellord1(X8,X9,X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) )
      & ( k2_relat_1(X10) = k3_relat_1(X9)
        | ~ r3_wellord1(X8,X9,X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) )
      & ( v2_funct_1(X10)
        | ~ r3_wellord1(X8,X9,X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(X11,k3_relat_1(X8))
        | ~ r2_hidden(k4_tarski(X11,X12),X8)
        | ~ r3_wellord1(X8,X9,X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(X12,k3_relat_1(X8))
        | ~ r2_hidden(k4_tarski(X11,X12),X8)
        | ~ r3_wellord1(X8,X9,X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(k4_tarski(k1_funct_1(X10,X11),k1_funct_1(X10,X12)),X9)
        | ~ r2_hidden(k4_tarski(X11,X12),X8)
        | ~ r3_wellord1(X8,X9,X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(X13,k3_relat_1(X8))
        | ~ r2_hidden(X14,k3_relat_1(X8))
        | ~ r2_hidden(k4_tarski(k1_funct_1(X10,X13),k1_funct_1(X10,X14)),X9)
        | r2_hidden(k4_tarski(X13,X14),X8)
        | ~ r3_wellord1(X8,X9,X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X8,X9,X10),esk2_3(X8,X9,X10)),X8)
        | ~ r2_hidden(esk1_3(X8,X9,X10),k3_relat_1(X8))
        | ~ r2_hidden(esk2_3(X8,X9,X10),k3_relat_1(X8))
        | ~ r2_hidden(k4_tarski(k1_funct_1(X10,esk1_3(X8,X9,X10)),k1_funct_1(X10,esk2_3(X8,X9,X10))),X9)
        | k1_relat_1(X10) != k3_relat_1(X8)
        | k2_relat_1(X10) != k3_relat_1(X9)
        | ~ v2_funct_1(X10)
        | r3_wellord1(X8,X9,X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(esk1_3(X8,X9,X10),k3_relat_1(X8))
        | r2_hidden(k4_tarski(esk1_3(X8,X9,X10),esk2_3(X8,X9,X10)),X8)
        | k1_relat_1(X10) != k3_relat_1(X8)
        | k2_relat_1(X10) != k3_relat_1(X9)
        | ~ v2_funct_1(X10)
        | r3_wellord1(X8,X9,X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(esk2_3(X8,X9,X10),k3_relat_1(X8))
        | r2_hidden(k4_tarski(esk1_3(X8,X9,X10),esk2_3(X8,X9,X10)),X8)
        | k1_relat_1(X10) != k3_relat_1(X8)
        | k2_relat_1(X10) != k3_relat_1(X9)
        | ~ v2_funct_1(X10)
        | r3_wellord1(X8,X9,X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(k4_tarski(k1_funct_1(X10,esk1_3(X8,X9,X10)),k1_funct_1(X10,esk2_3(X8,X9,X10))),X9)
        | r2_hidden(k4_tarski(esk1_3(X8,X9,X10),esk2_3(X8,X9,X10)),X8)
        | k1_relat_1(X10) != k3_relat_1(X8)
        | k2_relat_1(X10) != k3_relat_1(X9)
        | ~ v2_funct_1(X10)
        | r3_wellord1(X8,X9,X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_wellord1])])])])])])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & r3_wellord1(esk3_0,esk4_0,esk5_0)
    & r2_hidden(k4_tarski(esk6_0,esk7_0),esk3_0)
    & esk6_0 != esk7_0
    & ( ~ r2_hidden(k4_tarski(k1_funct_1(esk5_0,esk6_0),k1_funct_1(esk5_0,esk7_0)),esk4_0)
      | k1_funct_1(esk5_0,esk6_0) = k1_funct_1(esk5_0,esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(X1,X2),k1_funct_1(X1,X3)),X4)
    | ~ r2_hidden(k4_tarski(X2,X3),X5)
    | ~ r3_wellord1(X5,X4,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r3_wellord1(X2,X4,X5)
    | ~ v1_relat_1(X5)
    | ~ v1_funct_1(X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_10,plain,(
    ! [X6,X7] :
      ( ( X6 = k1_funct_1(k2_funct_1(X7),k1_funct_1(X7,X6))
        | ~ v2_funct_1(X7)
        | ~ r2_hidden(X6,k1_relat_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( X6 = k1_funct_1(k5_relat_1(X7,k2_funct_1(X7)),X6)
        | ~ v2_funct_1(X7)
        | ~ r2_hidden(X6,k1_relat_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).

cnf(c_0_11,negated_conjecture,
    ( k1_funct_1(esk5_0,esk6_0) = k1_funct_1(esk5_0,esk7_0)
    | ~ r2_hidden(k4_tarski(k1_funct_1(esk5_0,esk6_0),k1_funct_1(esk5_0,esk7_0)),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(X1,esk6_0),k1_funct_1(X1,esk7_0)),X2)
    | ~ r3_wellord1(esk3_0,X2,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])])).

cnf(c_0_13,negated_conjecture,
    ( r3_wellord1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( k1_relat_1(X1) = k3_relat_1(X2)
    | ~ r3_wellord1(X2,X3,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk7_0,k3_relat_1(esk3_0))
    | ~ r3_wellord1(esk3_0,X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_7]),c_0_8])])).

cnf(c_0_19,plain,
    ( v2_funct_1(X1)
    | ~ r3_wellord1(X2,X3,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r3_wellord1(X2,X4,X5)
    | ~ v1_relat_1(X5)
    | ~ v1_funct_1(X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_21,plain,
    ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
    | ~ v2_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( k1_funct_1(esk5_0,esk7_0) = k1_funct_1(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_23,negated_conjecture,
    ( k1_relat_1(esk5_0) = k3_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_13]),c_0_14]),c_0_15]),c_0_8]),c_0_16])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk7_0,k3_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_13]),c_0_14]),c_0_16]),c_0_15])])).

cnf(c_0_25,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_13]),c_0_14]),c_0_15]),c_0_8]),c_0_16])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk6_0,k3_relat_1(esk3_0))
    | ~ r3_wellord1(esk3_0,X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_7]),c_0_8])])).

cnf(c_0_27,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk5_0),k1_funct_1(esk5_0,esk6_0)) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_14]),c_0_16])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk6_0,k3_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_13]),c_0_14]),c_0_16]),c_0_15])])).

cnf(c_0_29,negated_conjecture,
    ( esk6_0 != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_27]),c_0_23]),c_0_28]),c_0_25]),c_0_14]),c_0_16])]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:45:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.030 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t45_wellord1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r3_wellord1(X1,X2,X3)=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X1)=>(X4=X5|(r2_hidden(k4_tarski(k1_funct_1(X3,X4),k1_funct_1(X3,X5)),X2)&k1_funct_1(X3,X4)!=k1_funct_1(X3,X5)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_wellord1)).
% 0.20/0.38  fof(d7_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r3_wellord1(X1,X2,X3)<=>(((k1_relat_1(X3)=k3_relat_1(X1)&k2_relat_1(X3)=k3_relat_1(X2))&v2_funct_1(X3))&![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X1)<=>((r2_hidden(X4,k3_relat_1(X1))&r2_hidden(X5,k3_relat_1(X1)))&r2_hidden(k4_tarski(k1_funct_1(X3,X4),k1_funct_1(X3,X5)),X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_wellord1)).
% 0.20/0.38  fof(t56_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k1_relat_1(X2)))=>(X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))&X1=k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 0.20/0.38  fof(c_0_3, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r3_wellord1(X1,X2,X3)=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X1)=>(X4=X5|(r2_hidden(k4_tarski(k1_funct_1(X3,X4),k1_funct_1(X3,X5)),X2)&k1_funct_1(X3,X4)!=k1_funct_1(X3,X5))))))))), inference(assume_negation,[status(cth)],[t45_wellord1])).
% 0.20/0.38  fof(c_0_4, plain, ![X8, X9, X10, X11, X12, X13, X14]:(((((k1_relat_1(X10)=k3_relat_1(X8)|~r3_wellord1(X8,X9,X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))|~v1_relat_1(X9)|~v1_relat_1(X8))&(k2_relat_1(X10)=k3_relat_1(X9)|~r3_wellord1(X8,X9,X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))|~v1_relat_1(X9)|~v1_relat_1(X8)))&(v2_funct_1(X10)|~r3_wellord1(X8,X9,X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))|~v1_relat_1(X9)|~v1_relat_1(X8)))&((((r2_hidden(X11,k3_relat_1(X8))|~r2_hidden(k4_tarski(X11,X12),X8)|~r3_wellord1(X8,X9,X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))|~v1_relat_1(X9)|~v1_relat_1(X8))&(r2_hidden(X12,k3_relat_1(X8))|~r2_hidden(k4_tarski(X11,X12),X8)|~r3_wellord1(X8,X9,X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))|~v1_relat_1(X9)|~v1_relat_1(X8)))&(r2_hidden(k4_tarski(k1_funct_1(X10,X11),k1_funct_1(X10,X12)),X9)|~r2_hidden(k4_tarski(X11,X12),X8)|~r3_wellord1(X8,X9,X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))|~v1_relat_1(X9)|~v1_relat_1(X8)))&(~r2_hidden(X13,k3_relat_1(X8))|~r2_hidden(X14,k3_relat_1(X8))|~r2_hidden(k4_tarski(k1_funct_1(X10,X13),k1_funct_1(X10,X14)),X9)|r2_hidden(k4_tarski(X13,X14),X8)|~r3_wellord1(X8,X9,X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))|~v1_relat_1(X9)|~v1_relat_1(X8))))&((~r2_hidden(k4_tarski(esk1_3(X8,X9,X10),esk2_3(X8,X9,X10)),X8)|(~r2_hidden(esk1_3(X8,X9,X10),k3_relat_1(X8))|~r2_hidden(esk2_3(X8,X9,X10),k3_relat_1(X8))|~r2_hidden(k4_tarski(k1_funct_1(X10,esk1_3(X8,X9,X10)),k1_funct_1(X10,esk2_3(X8,X9,X10))),X9))|(k1_relat_1(X10)!=k3_relat_1(X8)|k2_relat_1(X10)!=k3_relat_1(X9)|~v2_funct_1(X10))|r3_wellord1(X8,X9,X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))|~v1_relat_1(X9)|~v1_relat_1(X8))&(((r2_hidden(esk1_3(X8,X9,X10),k3_relat_1(X8))|r2_hidden(k4_tarski(esk1_3(X8,X9,X10),esk2_3(X8,X9,X10)),X8)|(k1_relat_1(X10)!=k3_relat_1(X8)|k2_relat_1(X10)!=k3_relat_1(X9)|~v2_funct_1(X10))|r3_wellord1(X8,X9,X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))|~v1_relat_1(X9)|~v1_relat_1(X8))&(r2_hidden(esk2_3(X8,X9,X10),k3_relat_1(X8))|r2_hidden(k4_tarski(esk1_3(X8,X9,X10),esk2_3(X8,X9,X10)),X8)|(k1_relat_1(X10)!=k3_relat_1(X8)|k2_relat_1(X10)!=k3_relat_1(X9)|~v2_funct_1(X10))|r3_wellord1(X8,X9,X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))|~v1_relat_1(X9)|~v1_relat_1(X8)))&(r2_hidden(k4_tarski(k1_funct_1(X10,esk1_3(X8,X9,X10)),k1_funct_1(X10,esk2_3(X8,X9,X10))),X9)|r2_hidden(k4_tarski(esk1_3(X8,X9,X10),esk2_3(X8,X9,X10)),X8)|(k1_relat_1(X10)!=k3_relat_1(X8)|k2_relat_1(X10)!=k3_relat_1(X9)|~v2_funct_1(X10))|r3_wellord1(X8,X9,X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))|~v1_relat_1(X9)|~v1_relat_1(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_wellord1])])])])])])).
% 0.20/0.38  fof(c_0_5, negated_conjecture, (v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&(r3_wellord1(esk3_0,esk4_0,esk5_0)&(r2_hidden(k4_tarski(esk6_0,esk7_0),esk3_0)&(esk6_0!=esk7_0&(~r2_hidden(k4_tarski(k1_funct_1(esk5_0,esk6_0),k1_funct_1(esk5_0,esk7_0)),esk4_0)|k1_funct_1(esk5_0,esk6_0)=k1_funct_1(esk5_0,esk7_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.20/0.38  cnf(c_0_6, plain, (r2_hidden(k4_tarski(k1_funct_1(X1,X2),k1_funct_1(X1,X3)),X4)|~r2_hidden(k4_tarski(X2,X3),X5)|~r3_wellord1(X5,X4,X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X4)|~v1_relat_1(X5)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.38  cnf(c_0_7, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk7_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_8, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_9, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~r3_wellord1(X2,X4,X5)|~v1_relat_1(X5)|~v1_funct_1(X5)|~v1_relat_1(X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.38  fof(c_0_10, plain, ![X6, X7]:((X6=k1_funct_1(k2_funct_1(X7),k1_funct_1(X7,X6))|(~v2_funct_1(X7)|~r2_hidden(X6,k1_relat_1(X7)))|(~v1_relat_1(X7)|~v1_funct_1(X7)))&(X6=k1_funct_1(k5_relat_1(X7,k2_funct_1(X7)),X6)|(~v2_funct_1(X7)|~r2_hidden(X6,k1_relat_1(X7)))|(~v1_relat_1(X7)|~v1_funct_1(X7)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).
% 0.20/0.38  cnf(c_0_11, negated_conjecture, (k1_funct_1(esk5_0,esk6_0)=k1_funct_1(esk5_0,esk7_0)|~r2_hidden(k4_tarski(k1_funct_1(esk5_0,esk6_0),k1_funct_1(esk5_0,esk7_0)),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_12, negated_conjecture, (r2_hidden(k4_tarski(k1_funct_1(X1,esk6_0),k1_funct_1(X1,esk7_0)),X2)|~r3_wellord1(esk3_0,X2,X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_7]), c_0_8])])).
% 0.20/0.38  cnf(c_0_13, negated_conjecture, (r3_wellord1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_14, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_16, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_17, plain, (k1_relat_1(X1)=k3_relat_1(X2)|~r3_wellord1(X2,X3,X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.38  cnf(c_0_18, negated_conjecture, (r2_hidden(esk7_0,k3_relat_1(esk3_0))|~r3_wellord1(esk3_0,X1,X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_7]), c_0_8])])).
% 0.20/0.38  cnf(c_0_19, plain, (v2_funct_1(X1)|~r3_wellord1(X2,X3,X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.38  cnf(c_0_20, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~r3_wellord1(X2,X4,X5)|~v1_relat_1(X5)|~v1_funct_1(X5)|~v1_relat_1(X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.38  cnf(c_0_21, plain, (X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))|~v2_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (k1_funct_1(esk5_0,esk7_0)=k1_funct_1(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_14]), c_0_15]), c_0_16])])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (k1_relat_1(esk5_0)=k3_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_13]), c_0_14]), c_0_15]), c_0_8]), c_0_16])])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(esk7_0,k3_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_13]), c_0_14]), c_0_16]), c_0_15])])).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (v2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_13]), c_0_14]), c_0_15]), c_0_8]), c_0_16])])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(esk6_0,k3_relat_1(esk3_0))|~r3_wellord1(esk3_0,X1,X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_7]), c_0_8])])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (k1_funct_1(k2_funct_1(esk5_0),k1_funct_1(esk5_0,esk6_0))=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_14]), c_0_16])])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(esk6_0,k3_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_13]), c_0_14]), c_0_16]), c_0_15])])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (esk6_0!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_27]), c_0_23]), c_0_28]), c_0_25]), c_0_14]), c_0_16])]), c_0_29]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 31
% 0.20/0.38  # Proof object clause steps            : 24
% 0.20/0.38  # Proof object formula steps           : 7
% 0.20/0.38  # Proof object conjectures             : 21
% 0.20/0.38  # Proof object clause conjectures      : 18
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 14
% 0.20/0.38  # Proof object initial formulas used   : 3
% 0.20/0.38  # Proof object generating inferences   : 10
% 0.20/0.38  # Proof object simplifying inferences  : 42
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 3
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 21
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 21
% 0.20/0.38  # Processed clauses                    : 51
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 0
% 0.20/0.38  # ...remaining for further processing  : 51
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 3
% 0.20/0.38  # Generated clauses                    : 33
% 0.20/0.38  # ...of the previous two non-trivial   : 32
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 33
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
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
% 0.20/0.38  # Current number of processed clauses  : 27
% 0.20/0.38  #    Positive orientable unit clauses  : 13
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 13
% 0.20/0.38  # Current number of unprocessed clauses: 20
% 0.20/0.38  # ...number of literals in the above   : 197
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 24
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 354
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 12
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.38  # Unit Clause-clause subsumption calls : 9
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 3
% 0.20/0.38  # BW rewrite match successes           : 3
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3555
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.034 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.037 s
% 0.20/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
