%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:38 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   63 (1609 expanded)
%              Number of clauses        :   52 ( 602 expanded)
%              Number of leaves         :    5 ( 370 expanded)
%              Depth                    :   18
%              Number of atoms          :  310 (10338 expanded)
%              Number of equality atoms :   91 (3908 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(t44_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X2)
              & k5_relat_1(X1,X2) = X1 )
           => X2 = k6_relat_1(k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(t34_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( X2 = k6_relat_1(X1)
      <=> ( k1_relat_1(X2) = X1
          & ! [X3] :
              ( r2_hidden(X3,X1)
             => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(c_0_5,plain,(
    ! [X23,X24,X25,X27,X28,X29,X31] :
      ( ( r2_hidden(esk5_3(X23,X24,X25),k1_relat_1(X23))
        | ~ r2_hidden(X25,X24)
        | X24 != k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( X25 = k1_funct_1(X23,esk5_3(X23,X24,X25))
        | ~ r2_hidden(X25,X24)
        | X24 != k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( ~ r2_hidden(X28,k1_relat_1(X23))
        | X27 != k1_funct_1(X23,X28)
        | r2_hidden(X27,X24)
        | X24 != k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( ~ r2_hidden(esk6_2(X23,X29),X29)
        | ~ r2_hidden(X31,k1_relat_1(X23))
        | esk6_2(X23,X29) != k1_funct_1(X23,X31)
        | X29 = k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( r2_hidden(esk7_2(X23,X29),k1_relat_1(X23))
        | r2_hidden(esk6_2(X23,X29),X29)
        | X29 = k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( esk6_2(X23,X29) = k1_funct_1(X23,esk7_2(X23,X29))
        | r2_hidden(esk6_2(X23,X29),X29)
        | X29 = k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( ( k2_relat_1(X1) = k1_relat_1(X2)
                & k5_relat_1(X1,X2) = X1 )
             => X2 = k6_relat_1(k1_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t44_funct_1])).

fof(c_0_7,plain,(
    ! [X20,X21,X22] :
      ( ( X22 != k1_funct_1(X20,X21)
        | r2_hidden(k4_tarski(X21,X22),X20)
        | ~ r2_hidden(X21,k1_relat_1(X20))
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( ~ r2_hidden(k4_tarski(X21,X22),X20)
        | X22 = k1_funct_1(X20,X21)
        | ~ r2_hidden(X21,k1_relat_1(X20))
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( X22 != k1_funct_1(X20,X21)
        | X22 = k1_xboole_0
        | r2_hidden(X21,k1_relat_1(X20))
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( X22 != k1_xboole_0
        | X22 = k1_funct_1(X20,X21)
        | r2_hidden(X21,k1_relat_1(X20))
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & v1_funct_1(esk9_0)
    & v1_relat_1(esk10_0)
    & v1_funct_1(esk10_0)
    & k2_relat_1(esk9_0) = k1_relat_1(esk10_0)
    & k5_relat_1(esk9_0,esk10_0) = esk9_0
    & esk10_0 != k6_relat_1(k1_relat_1(esk10_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_10,plain,
    ( X1 = k1_funct_1(X2,X3)
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_8])])).

cnf(c_0_12,negated_conjecture,
    ( k2_relat_1(esk9_0) = k1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k1_xboole_0 = k1_funct_1(X1,X2)
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X33,X34,X35] :
      ( ( k1_relat_1(X34) = X33
        | X34 != k6_relat_1(X33)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( ~ r2_hidden(X35,X33)
        | k1_funct_1(X34,X35) = X35
        | X34 != k6_relat_1(X33)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( r2_hidden(esk8_2(X33,X34),X33)
        | k1_relat_1(X34) != X33
        | X34 = k6_relat_1(X33)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( k1_funct_1(X34,esk8_2(X33,X34)) != esk8_2(X33,X34)
        | k1_relat_1(X34) != X33
        | X34 = k6_relat_1(X33)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk9_0,X1),k1_relat_1(esk10_0))
    | ~ r2_hidden(X1,k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_19,negated_conjecture,
    ( k1_funct_1(esk9_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_13]),c_0_14])])).

cnf(c_0_20,plain,
    ( X1 = k6_relat_1(X2)
    | k1_funct_1(X1,esk8_2(X2,X1)) != esk8_2(X2,X1)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( k1_funct_1(esk9_0,X1) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk9_0,X1),k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( X1 = k1_funct_1(X2,esk5_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_26,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | k1_funct_1(X1,esk8_2(k1_relat_1(X1),X1)) != esk8_2(k1_relat_1(X1),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( k1_funct_1(esk10_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_21]),c_0_22])])).

cnf(c_0_28,negated_conjecture,
    ( esk10_0 != k6_relat_1(k1_relat_1(esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_29,plain,(
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

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(esk9_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(k1_funct_1(esk9_0,X1),k1_funct_1(esk10_0,k1_funct_1(esk9_0,X1))),esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_21]),c_0_22])])).

cnf(c_0_31,plain,
    ( k1_funct_1(X1,esk5_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(esk8_2(X1,X2),X1)
    | X2 = k6_relat_1(X1)
    | k1_relat_1(X2) != X1
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk8_2(k1_relat_1(esk10_0),esk10_0),k1_relat_1(esk10_0))
    | esk8_2(k1_relat_1(esk10_0),esk10_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_21]),c_0_22])]),c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(X1,X4),X6)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X4),X5)
    | X6 != k5_relat_1(X3,X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(k4_tarski(X1,k1_funct_1(esk10_0,X1)),esk10_0)
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_13]),c_0_12]),c_0_14])])).

cnf(c_0_36,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | r2_hidden(esk8_2(k1_relat_1(X1),X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_2(k1_relat_1(esk10_0),esk10_0),k1_funct_1(esk10_0,esk8_2(k1_relat_1(esk10_0),esk10_0))),esk10_0)
    | esk8_2(k1_relat_1(esk10_0),esk10_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_33]),c_0_21]),c_0_22])])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X5,X2),X4)
    | ~ r2_hidden(k4_tarski(X1,X5),X3)
    | ~ v1_relat_1(k5_relat_1(X3,X4))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_2(k1_relat_1(esk10_0),esk10_0),k1_funct_1(esk10_0,esk8_2(k1_relat_1(esk10_0),esk10_0))),esk10_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_21]),c_0_22])]),c_0_28]),c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk10_0,esk8_2(k1_relat_1(esk10_0),esk10_0))),k5_relat_1(X2,esk10_0))
    | ~ r2_hidden(k4_tarski(X1,esk8_2(k1_relat_1(esk10_0),esk10_0)),X2)
    | ~ v1_relat_1(k5_relat_1(X2,esk10_0))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_22])])).

cnf(c_0_41,negated_conjecture,
    ( k5_relat_1(esk9_0,esk10_0) = esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_42,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_43,plain,
    ( X2 = k1_funct_1(X3,X1)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk10_0,esk8_2(k1_relat_1(esk10_0),esk10_0))),esk9_0)
    | ~ r2_hidden(k4_tarski(X1,esk8_2(k1_relat_1(esk10_0),esk10_0)),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_14])])).

cnf(c_0_45,plain,
    ( r2_hidden(esk5_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( k1_funct_1(esk9_0,X1) = k1_funct_1(esk10_0,esk8_2(k1_relat_1(esk10_0),esk10_0))
    | ~ r2_hidden(k4_tarski(X1,esk8_2(k1_relat_1(esk10_0),esk10_0)),esk9_0)
    | ~ r2_hidden(X1,k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_13]),c_0_14])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk5_3(esk9_0,k1_relat_1(esk10_0),X1),k1_relat_1(esk9_0))
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_48,negated_conjecture,
    ( k1_funct_1(esk9_0,esk5_3(esk9_0,k1_relat_1(esk10_0),X1)) = X1
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_49,negated_conjecture,
    ( k1_funct_1(esk9_0,esk5_3(esk9_0,k1_relat_1(esk10_0),X1)) = k1_funct_1(esk10_0,esk8_2(k1_relat_1(esk10_0),esk10_0))
    | ~ r2_hidden(k4_tarski(esk5_3(esk9_0,k1_relat_1(esk10_0),X1),esk8_2(k1_relat_1(esk10_0),esk10_0)),esk9_0)
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( k1_funct_1(esk9_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X1,k1_funct_1(esk9_0,X1)),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_19]),c_0_13]),c_0_14])])).

cnf(c_0_51,negated_conjecture,
    ( k1_funct_1(esk10_0,esk8_2(k1_relat_1(esk10_0),esk10_0)) = X1
    | ~ r2_hidden(k4_tarski(esk5_3(esk9_0,k1_relat_1(esk10_0),X1),esk8_2(k1_relat_1(esk10_0),esk10_0)),esk9_0)
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(k4_tarski(esk5_3(esk9_0,k1_relat_1(esk10_0),X1),X1),esk9_0)
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_31]),c_0_12]),c_0_13]),c_0_12]),c_0_14])])).

cnf(c_0_53,negated_conjecture,
    ( k1_funct_1(esk10_0,esk8_2(k1_relat_1(esk10_0),esk10_0)) = esk8_2(k1_relat_1(esk10_0),esk10_0)
    | esk8_2(k1_relat_1(esk10_0),esk10_0) = k1_xboole_0
    | ~ r2_hidden(esk8_2(k1_relat_1(esk10_0),esk10_0),k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_54,negated_conjecture,
    ( esk8_2(k1_relat_1(esk10_0),esk10_0) = k1_xboole_0
    | ~ r2_hidden(esk8_2(k1_relat_1(esk10_0),esk10_0),k1_relat_1(esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_53]),c_0_21]),c_0_22])]),c_0_28])).

cnf(c_0_55,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),k1_funct_1(X1,esk5_3(X1,k2_relat_1(X1),X2))),X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( esk8_2(k1_relat_1(esk10_0),esk10_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_36]),c_0_21]),c_0_22])]),c_0_28])).

cnf(c_0_57,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_31])).

cnf(c_0_58,negated_conjecture,
    ( k1_funct_1(esk10_0,k1_xboole_0) = X1
    | ~ r2_hidden(k4_tarski(esk5_3(esk9_0,k1_relat_1(esk10_0),X1),k1_xboole_0),esk9_0)
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_56]),c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(esk9_0,k1_relat_1(esk10_0),X1),X1),esk9_0)
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_56]),c_0_56])])).

cnf(c_0_61,negated_conjecture,
    ( k1_funct_1(esk10_0,k1_xboole_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_56]),c_0_21]),c_0_22])]),c_0_28])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:52:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.13/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.028 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.13/0.40  fof(t44_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k2_relat_1(X1)=k1_relat_1(X2)&k5_relat_1(X1,X2)=X1)=>X2=k6_relat_1(k1_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_1)).
% 0.13/0.40  fof(d4_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:((r2_hidden(X2,k1_relat_1(X1))=>(X3=k1_funct_1(X1,X2)<=>r2_hidden(k4_tarski(X2,X3),X1)))&(~(r2_hidden(X2,k1_relat_1(X1)))=>(X3=k1_funct_1(X1,X2)<=>X3=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 0.13/0.40  fof(t34_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k6_relat_1(X1)<=>(k1_relat_1(X2)=X1&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 0.13/0.40  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 0.13/0.40  fof(c_0_5, plain, ![X23, X24, X25, X27, X28, X29, X31]:((((r2_hidden(esk5_3(X23,X24,X25),k1_relat_1(X23))|~r2_hidden(X25,X24)|X24!=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(X25=k1_funct_1(X23,esk5_3(X23,X24,X25))|~r2_hidden(X25,X24)|X24!=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23))))&(~r2_hidden(X28,k1_relat_1(X23))|X27!=k1_funct_1(X23,X28)|r2_hidden(X27,X24)|X24!=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23))))&((~r2_hidden(esk6_2(X23,X29),X29)|(~r2_hidden(X31,k1_relat_1(X23))|esk6_2(X23,X29)!=k1_funct_1(X23,X31))|X29=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&((r2_hidden(esk7_2(X23,X29),k1_relat_1(X23))|r2_hidden(esk6_2(X23,X29),X29)|X29=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(esk6_2(X23,X29)=k1_funct_1(X23,esk7_2(X23,X29))|r2_hidden(esk6_2(X23,X29),X29)|X29=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.13/0.40  fof(c_0_6, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k2_relat_1(X1)=k1_relat_1(X2)&k5_relat_1(X1,X2)=X1)=>X2=k6_relat_1(k1_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t44_funct_1])).
% 0.13/0.40  fof(c_0_7, plain, ![X20, X21, X22]:(((X22!=k1_funct_1(X20,X21)|r2_hidden(k4_tarski(X21,X22),X20)|~r2_hidden(X21,k1_relat_1(X20))|(~v1_relat_1(X20)|~v1_funct_1(X20)))&(~r2_hidden(k4_tarski(X21,X22),X20)|X22=k1_funct_1(X20,X21)|~r2_hidden(X21,k1_relat_1(X20))|(~v1_relat_1(X20)|~v1_funct_1(X20))))&((X22!=k1_funct_1(X20,X21)|X22=k1_xboole_0|r2_hidden(X21,k1_relat_1(X20))|(~v1_relat_1(X20)|~v1_funct_1(X20)))&(X22!=k1_xboole_0|X22=k1_funct_1(X20,X21)|r2_hidden(X21,k1_relat_1(X20))|(~v1_relat_1(X20)|~v1_funct_1(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).
% 0.13/0.40  cnf(c_0_8, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.40  fof(c_0_9, negated_conjecture, ((v1_relat_1(esk9_0)&v1_funct_1(esk9_0))&((v1_relat_1(esk10_0)&v1_funct_1(esk10_0))&((k2_relat_1(esk9_0)=k1_relat_1(esk10_0)&k5_relat_1(esk9_0,esk10_0)=esk9_0)&esk10_0!=k6_relat_1(k1_relat_1(esk10_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.13/0.40  cnf(c_0_10, plain, (X1=k1_funct_1(X2,X3)|r2_hidden(X3,k1_relat_1(X2))|X1!=k1_xboole_0|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_11, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_8])])).
% 0.13/0.40  cnf(c_0_12, negated_conjecture, (k2_relat_1(esk9_0)=k1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  cnf(c_0_13, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  cnf(c_0_15, plain, (k1_xboole_0=k1_funct_1(X1,X2)|r2_hidden(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_10])).
% 0.13/0.40  fof(c_0_16, plain, ![X33, X34, X35]:(((k1_relat_1(X34)=X33|X34!=k6_relat_1(X33)|(~v1_relat_1(X34)|~v1_funct_1(X34)))&(~r2_hidden(X35,X33)|k1_funct_1(X34,X35)=X35|X34!=k6_relat_1(X33)|(~v1_relat_1(X34)|~v1_funct_1(X34))))&((r2_hidden(esk8_2(X33,X34),X33)|k1_relat_1(X34)!=X33|X34=k6_relat_1(X33)|(~v1_relat_1(X34)|~v1_funct_1(X34)))&(k1_funct_1(X34,esk8_2(X33,X34))!=esk8_2(X33,X34)|k1_relat_1(X34)!=X33|X34=k6_relat_1(X33)|(~v1_relat_1(X34)|~v1_funct_1(X34))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).
% 0.13/0.40  cnf(c_0_17, plain, (r2_hidden(k4_tarski(X3,X1),X2)|X1!=k1_funct_1(X2,X3)|~r2_hidden(X3,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_18, negated_conjecture, (r2_hidden(k1_funct_1(esk9_0,X1),k1_relat_1(esk10_0))|~r2_hidden(X1,k1_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_14])])).
% 0.13/0.40  cnf(c_0_19, negated_conjecture, (k1_funct_1(esk9_0,X1)=k1_xboole_0|r2_hidden(X1,k1_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_13]), c_0_14])])).
% 0.13/0.40  cnf(c_0_20, plain, (X1=k6_relat_1(X2)|k1_funct_1(X1,esk8_2(X2,X1))!=esk8_2(X2,X1)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  cnf(c_0_23, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_24, negated_conjecture, (k1_funct_1(esk9_0,X1)=k1_xboole_0|r2_hidden(k1_funct_1(esk9_0,X1),k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.40  cnf(c_0_25, plain, (X1=k1_funct_1(X2,esk5_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.40  cnf(c_0_26, plain, (k6_relat_1(k1_relat_1(X1))=X1|k1_funct_1(X1,esk8_2(k1_relat_1(X1),X1))!=esk8_2(k1_relat_1(X1),X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_20])).
% 0.13/0.40  cnf(c_0_27, negated_conjecture, (k1_funct_1(esk10_0,X1)=k1_xboole_0|r2_hidden(X1,k1_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_21]), c_0_22])])).
% 0.13/0.40  cnf(c_0_28, negated_conjecture, (esk10_0!=k6_relat_1(k1_relat_1(esk10_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  fof(c_0_29, plain, ![X7, X8, X9, X10, X11, X13, X14, X15, X18]:((((r2_hidden(k4_tarski(X10,esk1_5(X7,X8,X9,X10,X11)),X7)|~r2_hidden(k4_tarski(X10,X11),X9)|X9!=k5_relat_1(X7,X8)|~v1_relat_1(X9)|~v1_relat_1(X8)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(esk1_5(X7,X8,X9,X10,X11),X11),X8)|~r2_hidden(k4_tarski(X10,X11),X9)|X9!=k5_relat_1(X7,X8)|~v1_relat_1(X9)|~v1_relat_1(X8)|~v1_relat_1(X7)))&(~r2_hidden(k4_tarski(X13,X15),X7)|~r2_hidden(k4_tarski(X15,X14),X8)|r2_hidden(k4_tarski(X13,X14),X9)|X9!=k5_relat_1(X7,X8)|~v1_relat_1(X9)|~v1_relat_1(X8)|~v1_relat_1(X7)))&((~r2_hidden(k4_tarski(esk2_3(X7,X8,X9),esk3_3(X7,X8,X9)),X9)|(~r2_hidden(k4_tarski(esk2_3(X7,X8,X9),X18),X7)|~r2_hidden(k4_tarski(X18,esk3_3(X7,X8,X9)),X8))|X9=k5_relat_1(X7,X8)|~v1_relat_1(X9)|~v1_relat_1(X8)|~v1_relat_1(X7))&((r2_hidden(k4_tarski(esk2_3(X7,X8,X9),esk4_3(X7,X8,X9)),X7)|r2_hidden(k4_tarski(esk2_3(X7,X8,X9),esk3_3(X7,X8,X9)),X9)|X9=k5_relat_1(X7,X8)|~v1_relat_1(X9)|~v1_relat_1(X8)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(esk4_3(X7,X8,X9),esk3_3(X7,X8,X9)),X8)|r2_hidden(k4_tarski(esk2_3(X7,X8,X9),esk3_3(X7,X8,X9)),X9)|X9=k5_relat_1(X7,X8)|~v1_relat_1(X9)|~v1_relat_1(X8)|~v1_relat_1(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.13/0.40  cnf(c_0_30, negated_conjecture, (k1_funct_1(esk9_0,X1)=k1_xboole_0|r2_hidden(k4_tarski(k1_funct_1(esk9_0,X1),k1_funct_1(esk10_0,k1_funct_1(esk9_0,X1))),esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_21]), c_0_22])])).
% 0.13/0.40  cnf(c_0_31, plain, (k1_funct_1(X1,esk5_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_25])).
% 0.13/0.40  cnf(c_0_32, plain, (r2_hidden(esk8_2(X1,X2),X1)|X2=k6_relat_1(X1)|k1_relat_1(X2)!=X1|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_33, negated_conjecture, (r2_hidden(esk8_2(k1_relat_1(esk10_0),esk10_0),k1_relat_1(esk10_0))|esk8_2(k1_relat_1(esk10_0),esk10_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_21]), c_0_22])]), c_0_28])).
% 0.13/0.40  cnf(c_0_34, plain, (r2_hidden(k4_tarski(X1,X4),X6)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X2,X4),X5)|X6!=k5_relat_1(X3,X5)|~v1_relat_1(X6)|~v1_relat_1(X5)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.40  cnf(c_0_35, negated_conjecture, (X1=k1_xboole_0|r2_hidden(k4_tarski(X1,k1_funct_1(esk10_0,X1)),esk10_0)|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_13]), c_0_12]), c_0_14])])).
% 0.13/0.40  cnf(c_0_36, plain, (k6_relat_1(k1_relat_1(X1))=X1|r2_hidden(esk8_2(k1_relat_1(X1),X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_32])).
% 0.13/0.40  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(esk8_2(k1_relat_1(esk10_0),esk10_0),k1_funct_1(esk10_0,esk8_2(k1_relat_1(esk10_0),esk10_0))),esk10_0)|esk8_2(k1_relat_1(esk10_0),esk10_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_33]), c_0_21]), c_0_22])])).
% 0.13/0.40  cnf(c_0_38, plain, (r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))|~r2_hidden(k4_tarski(X5,X2),X4)|~r2_hidden(k4_tarski(X1,X5),X3)|~v1_relat_1(k5_relat_1(X3,X4))|~v1_relat_1(X4)|~v1_relat_1(X3)), inference(er,[status(thm)],[c_0_34])).
% 0.13/0.40  cnf(c_0_39, negated_conjecture, (r2_hidden(k4_tarski(esk8_2(k1_relat_1(esk10_0),esk10_0),k1_funct_1(esk10_0,esk8_2(k1_relat_1(esk10_0),esk10_0))),esk10_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_21]), c_0_22])]), c_0_28]), c_0_37])).
% 0.13/0.40  cnf(c_0_40, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk10_0,esk8_2(k1_relat_1(esk10_0),esk10_0))),k5_relat_1(X2,esk10_0))|~r2_hidden(k4_tarski(X1,esk8_2(k1_relat_1(esk10_0),esk10_0)),X2)|~v1_relat_1(k5_relat_1(X2,esk10_0))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_22])])).
% 0.13/0.40  cnf(c_0_41, negated_conjecture, (k5_relat_1(esk9_0,esk10_0)=esk9_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  cnf(c_0_42, plain, (r2_hidden(esk5_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.40  cnf(c_0_43, plain, (X2=k1_funct_1(X3,X1)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,k1_relat_1(X3))|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_44, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk10_0,esk8_2(k1_relat_1(esk10_0),esk10_0))),esk9_0)|~r2_hidden(k4_tarski(X1,esk8_2(k1_relat_1(esk10_0),esk10_0)),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_14])])).
% 0.13/0.40  cnf(c_0_45, plain, (r2_hidden(esk5_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_42])).
% 0.13/0.40  cnf(c_0_46, negated_conjecture, (k1_funct_1(esk9_0,X1)=k1_funct_1(esk10_0,esk8_2(k1_relat_1(esk10_0),esk10_0))|~r2_hidden(k4_tarski(X1,esk8_2(k1_relat_1(esk10_0),esk10_0)),esk9_0)|~r2_hidden(X1,k1_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_13]), c_0_14])])).
% 0.13/0.40  cnf(c_0_47, negated_conjecture, (r2_hidden(esk5_3(esk9_0,k1_relat_1(esk10_0),X1),k1_relat_1(esk9_0))|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_12]), c_0_13]), c_0_14])])).
% 0.13/0.40  cnf(c_0_48, negated_conjecture, (k1_funct_1(esk9_0,esk5_3(esk9_0,k1_relat_1(esk10_0),X1))=X1|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_12]), c_0_13]), c_0_14])])).
% 0.13/0.40  cnf(c_0_49, negated_conjecture, (k1_funct_1(esk9_0,esk5_3(esk9_0,k1_relat_1(esk10_0),X1))=k1_funct_1(esk10_0,esk8_2(k1_relat_1(esk10_0),esk10_0))|~r2_hidden(k4_tarski(esk5_3(esk9_0,k1_relat_1(esk10_0),X1),esk8_2(k1_relat_1(esk10_0),esk10_0)),esk9_0)|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.13/0.40  cnf(c_0_50, negated_conjecture, (k1_funct_1(esk9_0,X1)=k1_xboole_0|r2_hidden(k4_tarski(X1,k1_funct_1(esk9_0,X1)),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_19]), c_0_13]), c_0_14])])).
% 0.13/0.40  cnf(c_0_51, negated_conjecture, (k1_funct_1(esk10_0,esk8_2(k1_relat_1(esk10_0),esk10_0))=X1|~r2_hidden(k4_tarski(esk5_3(esk9_0,k1_relat_1(esk10_0),X1),esk8_2(k1_relat_1(esk10_0),esk10_0)),esk9_0)|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.40  cnf(c_0_52, negated_conjecture, (X1=k1_xboole_0|r2_hidden(k4_tarski(esk5_3(esk9_0,k1_relat_1(esk10_0),X1),X1),esk9_0)|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_31]), c_0_12]), c_0_13]), c_0_12]), c_0_14])])).
% 0.13/0.40  cnf(c_0_53, negated_conjecture, (k1_funct_1(esk10_0,esk8_2(k1_relat_1(esk10_0),esk10_0))=esk8_2(k1_relat_1(esk10_0),esk10_0)|esk8_2(k1_relat_1(esk10_0),esk10_0)=k1_xboole_0|~r2_hidden(esk8_2(k1_relat_1(esk10_0),esk10_0),k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.13/0.40  cnf(c_0_54, negated_conjecture, (esk8_2(k1_relat_1(esk10_0),esk10_0)=k1_xboole_0|~r2_hidden(esk8_2(k1_relat_1(esk10_0),esk10_0),k1_relat_1(esk10_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_53]), c_0_21]), c_0_22])]), c_0_28])).
% 0.13/0.40  cnf(c_0_55, plain, (r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),k1_funct_1(X1,esk5_3(X1,k2_relat_1(X1),X2))),X1)|~v1_funct_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_45])).
% 0.13/0.40  cnf(c_0_56, negated_conjecture, (esk8_2(k1_relat_1(esk10_0),esk10_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_36]), c_0_21]), c_0_22])]), c_0_28])).
% 0.13/0.40  cnf(c_0_57, plain, (r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)|~v1_funct_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_55, c_0_31])).
% 0.13/0.40  cnf(c_0_58, negated_conjecture, (k1_funct_1(esk10_0,k1_xboole_0)=X1|~r2_hidden(k4_tarski(esk5_3(esk9_0,k1_relat_1(esk10_0),X1),k1_xboole_0),esk9_0)|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_56]), c_0_56])).
% 0.13/0.40  cnf(c_0_59, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(esk9_0,k1_relat_1(esk10_0),X1),X1),esk9_0)|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_12]), c_0_13]), c_0_14])])).
% 0.13/0.40  cnf(c_0_60, negated_conjecture, (r2_hidden(k1_xboole_0,k1_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_56]), c_0_56])])).
% 0.13/0.40  cnf(c_0_61, negated_conjecture, (k1_funct_1(esk10_0,k1_xboole_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_56]), c_0_21]), c_0_22])]), c_0_28])).
% 0.13/0.40  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])]), c_0_61]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 63
% 0.13/0.40  # Proof object clause steps            : 52
% 0.13/0.40  # Proof object formula steps           : 11
% 0.13/0.40  # Proof object conjectures             : 36
% 0.13/0.40  # Proof object clause conjectures      : 33
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 16
% 0.13/0.40  # Proof object initial formulas used   : 5
% 0.13/0.40  # Proof object generating inferences   : 26
% 0.13/0.40  # Proof object simplifying inferences  : 79
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 5
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 27
% 0.13/0.40  # Removed in clause preprocessing      : 0
% 0.13/0.40  # Initial clauses in saturation        : 27
% 0.13/0.40  # Processed clauses                    : 214
% 0.13/0.40  # ...of these trivial                  : 6
% 0.13/0.40  # ...subsumed                          : 37
% 0.13/0.40  # ...remaining for further processing  : 171
% 0.13/0.40  # Other redundant clauses eliminated   : 15
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 20
% 0.13/0.40  # Backward-rewritten                   : 28
% 0.13/0.40  # Generated clauses                    : 649
% 0.13/0.40  # ...of the previous two non-trivial   : 635
% 0.13/0.40  # Contextual simplify-reflections      : 4
% 0.13/0.40  # Paramodulations                      : 628
% 0.13/0.40  # Factorizations                       : 7
% 0.13/0.40  # Equation resolutions                 : 15
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 84
% 0.13/0.40  #    Positive orientable unit clauses  : 9
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 2
% 0.13/0.40  #    Non-unit-clauses                  : 73
% 0.13/0.40  # Current number of unprocessed clauses: 471
% 0.13/0.40  # ...number of literals in the above   : 2618
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 74
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 2450
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 834
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 58
% 0.13/0.40  # Unit Clause-clause subsumption calls : 118
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 3
% 0.13/0.40  # BW rewrite match successes           : 3
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 23630
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.055 s
% 0.13/0.40  # System time              : 0.006 s
% 0.13/0.40  # Total time               : 0.062 s
% 0.13/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
