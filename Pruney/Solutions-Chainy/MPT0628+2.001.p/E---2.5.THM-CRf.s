%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:16 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 393 expanded)
%              Number of clauses        :   30 ( 139 expanded)
%              Number of leaves         :    7 (  95 expanded)
%              Depth                    :   11
%              Number of atoms          :  235 (2125 expanded)
%              Number of equality atoms :   43 ( 375 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t23_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(X2))
           => k1_funct_1(k5_relat_1(X2,X3),X1) = k1_funct_1(X3,k1_funct_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

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

fof(c_0_7,plain,(
    ! [X22,X23,X24] :
      ( ( X24 != k1_funct_1(X22,X23)
        | r2_hidden(k4_tarski(X23,X24),X22)
        | ~ r2_hidden(X23,k1_relat_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( ~ r2_hidden(k4_tarski(X23,X24),X22)
        | X24 = k1_funct_1(X22,X23)
        | ~ r2_hidden(X23,k1_relat_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( X24 != k1_funct_1(X22,X23)
        | X24 = k1_xboole_0
        | r2_hidden(X23,k1_relat_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( X24 != k1_xboole_0
        | X24 = k1_funct_1(X22,X23)
        | r2_hidden(X23,k1_relat_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ( r2_hidden(X1,k1_relat_1(X2))
             => k1_funct_1(k5_relat_1(X2,X3),X1) = k1_funct_1(X3,k1_funct_1(X2,X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_funct_1])).

fof(c_0_9,plain,(
    ! [X7,X8,X9,X10,X11,X13,X14,X15,X18] :
      ( ( r2_hidden(k4_tarski(X10,esk1_5(X7,X8,X9,X10,X11)),X7)
        | ~ r2_hidden(k4_tarski(X10,X11),X9)
        | X9 != k5_relat_1(X7,X8)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(esk1_5(X7,X8,X9,X10,X11),X11),X8)
        | ~ r2_hidden(k4_tarski(X10,X11),X9)
        | X9 != k5_relat_1(X7,X8)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(X13,X15),X7)
        | ~ r2_hidden(k4_tarski(X15,X14),X8)
        | r2_hidden(k4_tarski(X13,X14),X9)
        | X9 != k5_relat_1(X7,X8)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(esk2_3(X7,X8,X9),esk3_3(X7,X8,X9)),X9)
        | ~ r2_hidden(k4_tarski(esk2_3(X7,X8,X9),X18),X7)
        | ~ r2_hidden(k4_tarski(X18,esk3_3(X7,X8,X9)),X8)
        | X9 = k5_relat_1(X7,X8)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(esk2_3(X7,X8,X9),esk4_3(X7,X8,X9)),X7)
        | r2_hidden(k4_tarski(esk2_3(X7,X8,X9),esk3_3(X7,X8,X9)),X9)
        | X9 = k5_relat_1(X7,X8)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(esk4_3(X7,X8,X9),esk3_3(X7,X8,X9)),X8)
        | r2_hidden(k4_tarski(esk2_3(X7,X8,X9),esk3_3(X7,X8,X9)),X9)
        | X9 = k5_relat_1(X7,X8)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_10,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ v1_relat_1(X21)
      | v1_relat_1(k5_relat_1(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_11,plain,
    ( X1 = k1_funct_1(X2,X3)
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & r2_hidden(esk5_0,k1_relat_1(esk6_0))
    & k1_funct_1(k5_relat_1(esk6_0,esk7_0),esk5_0) != k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_13,plain,(
    ! [X30,X31,X32] :
      ( ( r2_hidden(X30,k1_relat_1(X32))
        | ~ r2_hidden(k4_tarski(X30,X31),X32)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( X31 = k1_funct_1(X32,X30)
        | ~ r2_hidden(k4_tarski(X30,X31),X32)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( ~ r2_hidden(X30,k1_relat_1(X32))
        | X31 != k1_funct_1(X32,X30)
        | r2_hidden(k4_tarski(X30,X31),X32)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,X4),X6)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X4),X5)
    | X6 != k5_relat_1(X3,X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X5,X2),X4)
    | ~ r2_hidden(k4_tarski(X1,X5),X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( k1_funct_1(esk7_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ v1_funct_1(k5_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( k1_funct_1(esk7_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X1,k1_funct_1(esk7_0,X1)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_18]),c_0_19])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_29,plain,(
    ! [X25,X26] :
      ( ( v1_relat_1(k5_relat_1(X25,X26))
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( v1_funct_1(k5_relat_1(X25,X26))
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(esk7_0,X1) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(k5_relat_1(X3,esk7_0)))
    | ~ v1_funct_1(k5_relat_1(X3,esk7_0))
    | ~ r2_hidden(k4_tarski(X2,X1),X3)
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_19])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,k1_funct_1(esk6_0,esk5_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_32,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_33,plain,(
    ! [X27,X28,X29] :
      ( ~ v1_relat_1(X28)
      | ~ v1_funct_1(X28)
      | ~ v1_relat_1(X29)
      | ~ v1_funct_1(X29)
      | ~ r2_hidden(X27,k1_relat_1(k5_relat_1(X29,X28)))
      | k1_funct_1(k5_relat_1(X29,X28),X27) = k1_funct_1(X28,k1_funct_1(X29,X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk5_0)) = k1_xboole_0
    | r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk6_0,esk7_0)))
    | ~ v1_funct_1(k5_relat_1(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_28])])).

cnf(c_0_35,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),X3) = k1_xboole_0
    | r2_hidden(X3,k1_relat_1(k5_relat_1(X1,X2)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_32]),c_0_15])).

cnf(c_0_36,plain,
    ( k1_funct_1(k5_relat_1(X2,X1),X3) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk5_0)) = k1_xboole_0
    | r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk6_0,esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_32]),c_0_18]),c_0_27]),c_0_19]),c_0_28])])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk6_0,esk7_0),esk5_0) != k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk6_0,X1),X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(k5_relat_1(esk6_0,X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_27]),c_0_28])])).

cnf(c_0_40,negated_conjecture,
    ( k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk5_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_27]),c_0_18]),c_0_28]),c_0_19])]),c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk6_0,esk7_0),X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(k5_relat_1(esk6_0,esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_18]),c_0_19])])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk6_0,esk7_0),esk5_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_38,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk6_0,esk7_0),X1) = k1_funct_1(esk7_0,k1_funct_1(esk6_0,X1))
    | k1_funct_1(k5_relat_1(esk6_0,esk7_0),X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_41]),c_0_27]),c_0_18]),c_0_28]),c_0_19])])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_40])]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:48:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.21/0.39  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.027 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(d4_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:((r2_hidden(X2,k1_relat_1(X1))=>(X3=k1_funct_1(X1,X2)<=>r2_hidden(k4_tarski(X2,X3),X1)))&(~(r2_hidden(X2,k1_relat_1(X1)))=>(X3=k1_funct_1(X1,X2)<=>X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 0.21/0.39  fof(t23_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(X2))=>k1_funct_1(k5_relat_1(X2,X3),X1)=k1_funct_1(X3,k1_funct_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 0.21/0.39  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 0.21/0.39  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.21/0.39  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.21/0.39  fof(fc2_funct_1, axiom, ![X1, X2]:((((v1_relat_1(X1)&v1_funct_1(X1))&v1_relat_1(X2))&v1_funct_1(X2))=>(v1_relat_1(k5_relat_1(X1,X2))&v1_funct_1(k5_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 0.21/0.39  fof(t22_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))=>k1_funct_1(k5_relat_1(X3,X2),X1)=k1_funct_1(X2,k1_funct_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 0.21/0.39  fof(c_0_7, plain, ![X22, X23, X24]:(((X24!=k1_funct_1(X22,X23)|r2_hidden(k4_tarski(X23,X24),X22)|~r2_hidden(X23,k1_relat_1(X22))|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(~r2_hidden(k4_tarski(X23,X24),X22)|X24=k1_funct_1(X22,X23)|~r2_hidden(X23,k1_relat_1(X22))|(~v1_relat_1(X22)|~v1_funct_1(X22))))&((X24!=k1_funct_1(X22,X23)|X24=k1_xboole_0|r2_hidden(X23,k1_relat_1(X22))|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(X24!=k1_xboole_0|X24=k1_funct_1(X22,X23)|r2_hidden(X23,k1_relat_1(X22))|(~v1_relat_1(X22)|~v1_funct_1(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).
% 0.21/0.39  fof(c_0_8, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(X2))=>k1_funct_1(k5_relat_1(X2,X3),X1)=k1_funct_1(X3,k1_funct_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t23_funct_1])).
% 0.21/0.39  fof(c_0_9, plain, ![X7, X8, X9, X10, X11, X13, X14, X15, X18]:((((r2_hidden(k4_tarski(X10,esk1_5(X7,X8,X9,X10,X11)),X7)|~r2_hidden(k4_tarski(X10,X11),X9)|X9!=k5_relat_1(X7,X8)|~v1_relat_1(X9)|~v1_relat_1(X8)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(esk1_5(X7,X8,X9,X10,X11),X11),X8)|~r2_hidden(k4_tarski(X10,X11),X9)|X9!=k5_relat_1(X7,X8)|~v1_relat_1(X9)|~v1_relat_1(X8)|~v1_relat_1(X7)))&(~r2_hidden(k4_tarski(X13,X15),X7)|~r2_hidden(k4_tarski(X15,X14),X8)|r2_hidden(k4_tarski(X13,X14),X9)|X9!=k5_relat_1(X7,X8)|~v1_relat_1(X9)|~v1_relat_1(X8)|~v1_relat_1(X7)))&((~r2_hidden(k4_tarski(esk2_3(X7,X8,X9),esk3_3(X7,X8,X9)),X9)|(~r2_hidden(k4_tarski(esk2_3(X7,X8,X9),X18),X7)|~r2_hidden(k4_tarski(X18,esk3_3(X7,X8,X9)),X8))|X9=k5_relat_1(X7,X8)|~v1_relat_1(X9)|~v1_relat_1(X8)|~v1_relat_1(X7))&((r2_hidden(k4_tarski(esk2_3(X7,X8,X9),esk4_3(X7,X8,X9)),X7)|r2_hidden(k4_tarski(esk2_3(X7,X8,X9),esk3_3(X7,X8,X9)),X9)|X9=k5_relat_1(X7,X8)|~v1_relat_1(X9)|~v1_relat_1(X8)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(esk4_3(X7,X8,X9),esk3_3(X7,X8,X9)),X8)|r2_hidden(k4_tarski(esk2_3(X7,X8,X9),esk3_3(X7,X8,X9)),X9)|X9=k5_relat_1(X7,X8)|~v1_relat_1(X9)|~v1_relat_1(X8)|~v1_relat_1(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.21/0.39  fof(c_0_10, plain, ![X20, X21]:(~v1_relat_1(X20)|~v1_relat_1(X21)|v1_relat_1(k5_relat_1(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.21/0.39  cnf(c_0_11, plain, (X1=k1_funct_1(X2,X3)|r2_hidden(X3,k1_relat_1(X2))|X1!=k1_xboole_0|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.39  fof(c_0_12, negated_conjecture, ((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&(r2_hidden(esk5_0,k1_relat_1(esk6_0))&k1_funct_1(k5_relat_1(esk6_0,esk7_0),esk5_0)!=k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.21/0.39  fof(c_0_13, plain, ![X30, X31, X32]:(((r2_hidden(X30,k1_relat_1(X32))|~r2_hidden(k4_tarski(X30,X31),X32)|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(X31=k1_funct_1(X32,X30)|~r2_hidden(k4_tarski(X30,X31),X32)|(~v1_relat_1(X32)|~v1_funct_1(X32))))&(~r2_hidden(X30,k1_relat_1(X32))|X31!=k1_funct_1(X32,X30)|r2_hidden(k4_tarski(X30,X31),X32)|(~v1_relat_1(X32)|~v1_funct_1(X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.21/0.39  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,X4),X6)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X2,X4),X5)|X6!=k5_relat_1(X3,X5)|~v1_relat_1(X6)|~v1_relat_1(X5)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.39  cnf(c_0_15, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_16, plain, (r2_hidden(k4_tarski(X3,X1),X2)|X1!=k1_funct_1(X2,X3)|~r2_hidden(X3,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.39  cnf(c_0_17, plain, (k1_funct_1(X1,X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_18, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_20, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.39  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))|~r2_hidden(k4_tarski(X5,X2),X4)|~r2_hidden(k4_tarski(X1,X5),X3)|~v1_relat_1(X4)|~v1_relat_1(X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]), c_0_15])).
% 0.21/0.39  cnf(c_0_22, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_23, negated_conjecture, (k1_funct_1(esk7_0,X1)=k1_xboole_0|r2_hidden(X1,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.21/0.39  cnf(c_0_24, plain, (r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))|~v1_funct_1(k5_relat_1(X2,X3))|~r2_hidden(k4_tarski(X4,X5),X3)|~r2_hidden(k4_tarski(X1,X4),X2)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_15])).
% 0.21/0.39  cnf(c_0_25, negated_conjecture, (k1_funct_1(esk7_0,X1)=k1_xboole_0|r2_hidden(k4_tarski(X1,k1_funct_1(esk7_0,X1)),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_18]), c_0_19])])).
% 0.21/0.39  cnf(c_0_26, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  fof(c_0_29, plain, ![X25, X26]:((v1_relat_1(k5_relat_1(X25,X26))|(~v1_relat_1(X25)|~v1_funct_1(X25)|~v1_relat_1(X26)|~v1_funct_1(X26)))&(v1_funct_1(k5_relat_1(X25,X26))|(~v1_relat_1(X25)|~v1_funct_1(X25)|~v1_relat_1(X26)|~v1_funct_1(X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).
% 0.21/0.39  cnf(c_0_30, negated_conjecture, (k1_funct_1(esk7_0,X1)=k1_xboole_0|r2_hidden(X2,k1_relat_1(k5_relat_1(X3,esk7_0)))|~v1_funct_1(k5_relat_1(X3,esk7_0))|~r2_hidden(k4_tarski(X2,X1),X3)|~v1_relat_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_19])])).
% 0.21/0.39  cnf(c_0_31, negated_conjecture, (r2_hidden(k4_tarski(esk5_0,k1_funct_1(esk6_0,esk5_0)),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_26]), c_0_27]), c_0_28])])).
% 0.21/0.39  cnf(c_0_32, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.39  fof(c_0_33, plain, ![X27, X28, X29]:(~v1_relat_1(X28)|~v1_funct_1(X28)|(~v1_relat_1(X29)|~v1_funct_1(X29)|(~r2_hidden(X27,k1_relat_1(k5_relat_1(X29,X28)))|k1_funct_1(k5_relat_1(X29,X28),X27)=k1_funct_1(X28,k1_funct_1(X29,X27))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).
% 0.21/0.39  cnf(c_0_34, negated_conjecture, (k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk5_0))=k1_xboole_0|r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk6_0,esk7_0)))|~v1_funct_1(k5_relat_1(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_28])])).
% 0.21/0.39  cnf(c_0_35, plain, (k1_funct_1(k5_relat_1(X1,X2),X3)=k1_xboole_0|r2_hidden(X3,k1_relat_1(k5_relat_1(X1,X2)))|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_32]), c_0_15])).
% 0.21/0.39  cnf(c_0_36, plain, (k1_funct_1(k5_relat_1(X2,X1),X3)=k1_funct_1(X1,k1_funct_1(X2,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.39  cnf(c_0_37, negated_conjecture, (k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk5_0))=k1_xboole_0|r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk6_0,esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_32]), c_0_18]), c_0_27]), c_0_19]), c_0_28])])).
% 0.21/0.39  cnf(c_0_38, negated_conjecture, (k1_funct_1(k5_relat_1(esk6_0,esk7_0),esk5_0)!=k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_39, negated_conjecture, (k1_funct_1(k5_relat_1(esk6_0,X1),X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(k5_relat_1(esk6_0,X1)))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_27]), c_0_28])])).
% 0.21/0.39  cnf(c_0_40, negated_conjecture, (k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk5_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_27]), c_0_18]), c_0_28]), c_0_19])]), c_0_38])).
% 0.21/0.39  cnf(c_0_41, negated_conjecture, (k1_funct_1(k5_relat_1(esk6_0,esk7_0),X1)=k1_xboole_0|r2_hidden(X1,k1_relat_1(k5_relat_1(esk6_0,esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_18]), c_0_19])])).
% 0.21/0.39  cnf(c_0_42, negated_conjecture, (k1_funct_1(k5_relat_1(esk6_0,esk7_0),esk5_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_38, c_0_40])).
% 0.21/0.39  cnf(c_0_43, negated_conjecture, (k1_funct_1(k5_relat_1(esk6_0,esk7_0),X1)=k1_funct_1(esk7_0,k1_funct_1(esk6_0,X1))|k1_funct_1(k5_relat_1(esk6_0,esk7_0),X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_41]), c_0_27]), c_0_18]), c_0_28]), c_0_19])])).
% 0.21/0.39  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_40])]), c_0_42]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 45
% 0.21/0.39  # Proof object clause steps            : 30
% 0.21/0.39  # Proof object formula steps           : 15
% 0.21/0.39  # Proof object conjectures             : 21
% 0.21/0.39  # Proof object clause conjectures      : 18
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 13
% 0.21/0.39  # Proof object initial formulas used   : 7
% 0.21/0.39  # Proof object generating inferences   : 13
% 0.21/0.39  # Proof object simplifying inferences  : 42
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 7
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 23
% 0.21/0.39  # Removed in clause preprocessing      : 0
% 0.21/0.39  # Initial clauses in saturation        : 23
% 0.21/0.39  # Processed clauses                    : 122
% 0.21/0.39  # ...of these trivial                  : 0
% 0.21/0.39  # ...subsumed                          : 15
% 0.21/0.39  # ...remaining for further processing  : 107
% 0.21/0.39  # Other redundant clauses eliminated   : 7
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 8
% 0.21/0.39  # Backward-rewritten                   : 2
% 0.21/0.39  # Generated clauses                    : 380
% 0.21/0.39  # ...of the previous two non-trivial   : 374
% 0.21/0.39  # Contextual simplify-reflections      : 7
% 0.21/0.39  # Paramodulations                      : 370
% 0.21/0.39  # Factorizations                       : 3
% 0.21/0.39  # Equation resolutions                 : 7
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 71
% 0.21/0.39  #    Positive orientable unit clauses  : 7
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 1
% 0.21/0.39  #    Non-unit-clauses                  : 63
% 0.21/0.39  # Current number of unprocessed clauses: 292
% 0.21/0.39  # ...number of literals in the above   : 1848
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 29
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 1242
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 329
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 30
% 0.21/0.39  # Unit Clause-clause subsumption calls : 9
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 1
% 0.21/0.39  # BW rewrite match successes           : 1
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 12961
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.043 s
% 0.21/0.39  # System time              : 0.003 s
% 0.21/0.39  # Total time               : 0.047 s
% 0.21/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
