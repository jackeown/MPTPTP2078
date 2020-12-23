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
% DateTime   : Thu Dec  3 10:53:18 EST 2020

% Result     : Theorem 1.03s
% Output     : CNFRefutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 738 expanded)
%              Number of clauses        :   37 ( 275 expanded)
%              Number of leaves         :    8 ( 200 expanded)
%              Depth                    :   11
%              Number of atoms          :  225 (3433 expanded)
%              Number of equality atoms :  101 (1651 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( X2 = k6_relat_1(X1)
      <=> ( k1_relat_1(X2) = X1
          & ! [X3] :
              ( r2_hidden(X3,X1)
             => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

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

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t23_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(X2))
           => k1_funct_1(k5_relat_1(X2,X3),X1) = k1_funct_1(X3,k1_funct_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(t78_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(t9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k1_relat_1(X1) = k1_relat_1(X2)
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( X2 = k6_relat_1(X1)
        <=> ( k1_relat_1(X2) = X1
            & ! [X3] :
                ( r2_hidden(X3,X1)
               => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_funct_1])).

fof(c_0_9,plain,(
    ! [X8,X9,X10,X12,X13,X14,X16] :
      ( ( r2_hidden(esk1_3(X8,X9,X10),k1_relat_1(X8))
        | ~ r2_hidden(X10,X9)
        | X9 != k2_relat_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( X10 = k1_funct_1(X8,esk1_3(X8,X9,X10))
        | ~ r2_hidden(X10,X9)
        | X9 != k2_relat_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( ~ r2_hidden(X13,k1_relat_1(X8))
        | X12 != k1_funct_1(X8,X13)
        | r2_hidden(X12,X9)
        | X9 != k2_relat_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( ~ r2_hidden(esk2_2(X8,X14),X14)
        | ~ r2_hidden(X16,k1_relat_1(X8))
        | esk2_2(X8,X14) != k1_funct_1(X8,X16)
        | X14 = k2_relat_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( r2_hidden(esk3_2(X8,X14),k1_relat_1(X8))
        | r2_hidden(esk2_2(X8,X14),X14)
        | X14 = k2_relat_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( esk2_2(X8,X14) = k1_funct_1(X8,esk3_2(X8,X14))
        | r2_hidden(esk2_2(X8,X14),X14)
        | X14 = k2_relat_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_10,plain,(
    ! [X5] :
      ( k1_relat_1(k6_relat_1(X5)) = X5
      & k2_relat_1(k6_relat_1(X5)) = X5 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_11,plain,(
    ! [X18] :
      ( v1_relat_1(k6_relat_1(X18))
      & v1_funct_1(k6_relat_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_12,negated_conjecture,(
    ! [X31] :
      ( v1_relat_1(esk6_0)
      & v1_funct_1(esk6_0)
      & ( r2_hidden(esk7_0,esk5_0)
        | k1_relat_1(esk6_0) != esk5_0
        | esk6_0 != k6_relat_1(esk5_0) )
      & ( k1_funct_1(esk6_0,esk7_0) != esk7_0
        | k1_relat_1(esk6_0) != esk5_0
        | esk6_0 != k6_relat_1(esk5_0) )
      & ( k1_relat_1(esk6_0) = esk5_0
        | esk6_0 = k6_relat_1(esk5_0) )
      & ( ~ r2_hidden(X31,esk5_0)
        | k1_funct_1(esk6_0,X31) = X31
        | esk6_0 = k6_relat_1(esk5_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])).

fof(c_0_13,plain,(
    ! [X22,X23,X24] :
      ( ~ v1_relat_1(X23)
      | ~ v1_funct_1(X23)
      | ~ v1_relat_1(X24)
      | ~ v1_funct_1(X24)
      | ~ r2_hidden(X22,k1_relat_1(X23))
      | k1_funct_1(k5_relat_1(X23,X24),X22) = k1_funct_1(X24,k1_funct_1(X23,X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = X1
    | esk6_0 = k6_relat_1(esk5_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),X3) = k1_funct_1(X2,k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | X1 != k1_funct_1(k6_relat_1(X2),X3)
    | ~ r2_hidden(X3,X2) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_18])])])).

fof(c_0_24,plain,(
    ! [X6] :
      ( ~ v1_relat_1(X6)
      | k5_relat_1(k6_relat_1(k1_relat_1(X6)),X6) = X6 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).

cnf(c_0_25,negated_conjecture,
    ( k1_funct_1(k5_relat_1(X1,esk6_0),X2) = k1_funct_1(X1,X2)
    | k6_relat_1(esk5_0) = esk6_0
    | ~ r2_hidden(k1_funct_1(X1,X2),esk5_0)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_26,plain,
    ( r2_hidden(k1_funct_1(k6_relat_1(X1),X2),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk5_0
    | esk6_0 = k6_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_29,plain,(
    ! [X25,X26] :
      ( ( r2_hidden(esk4_2(X25,X26),k1_relat_1(X25))
        | k1_relat_1(X25) != k1_relat_1(X26)
        | X25 = X26
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( k1_funct_1(X25,esk4_2(X25,X26)) != k1_funct_1(X26,esk4_2(X25,X26))
        | k1_relat_1(X25) != k1_relat_1(X26)
        | X25 = X26
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).

fof(c_0_30,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k5_relat_1(X7,k6_relat_1(k2_relat_1(X7))) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

cnf(c_0_31,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k6_relat_1(esk5_0),esk6_0),X1) = k1_funct_1(k6_relat_1(esk5_0),X1)
    | k6_relat_1(esk5_0) = esk6_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_15]),c_0_17]),c_0_18])])).

cnf(c_0_32,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk5_0),esk6_0) = esk6_0
    | k6_relat_1(esk5_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_22])])).

cnf(c_0_33,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | X1 = X2
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( X1 = k1_funct_1(X2,esk1_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( X1 = X2
    | k1_funct_1(X1,esk4_2(X1,X2)) != k1_funct_1(X2,esk4_2(X1,X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(k6_relat_1(esk5_0),X1) = k1_funct_1(esk6_0,X1)
    | k6_relat_1(esk5_0) = esk6_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( k6_relat_1(X1) = X2
    | r2_hidden(esk4_2(k6_relat_1(X1),X2),X1)
    | X1 != k1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_15]),c_0_17]),c_0_18])])).

cnf(c_0_40,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),esk1_3(X1,X3,X4)) = k1_funct_1(X2,X4)
    | X3 != k2_relat_1(X1)
    | ~ r2_hidden(X4,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_34]),c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k5_relat_1(esk6_0,k6_relat_1(k2_relat_1(esk6_0))) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_22])).

cnf(c_0_42,negated_conjecture,
    ( k6_relat_1(esk5_0) = esk6_0
    | k6_relat_1(esk5_0) = X1
    | k1_funct_1(esk6_0,esk4_2(k6_relat_1(esk5_0),X1)) != k1_funct_1(X1,esk4_2(k6_relat_1(esk5_0),X1))
    | k1_relat_1(X1) != esk5_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_15]),c_0_17]),c_0_18])]),c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( k1_funct_1(esk6_0,esk1_3(esk6_0,X1,X2)) = k1_funct_1(k6_relat_1(k2_relat_1(esk6_0)),X2)
    | X1 != k2_relat_1(esk6_0)
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_17]),c_0_21]),c_0_18]),c_0_22])])).

cnf(c_0_44,negated_conjecture,
    ( k1_funct_1(esk6_0,esk7_0) != esk7_0
    | k1_relat_1(esk6_0) != esk5_0
    | esk6_0 != k6_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( k6_relat_1(esk5_0) = esk6_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_42]),c_0_21]),c_0_22])]),c_0_28])).

cnf(c_0_46,negated_conjecture,
    ( k1_funct_1(k6_relat_1(k2_relat_1(esk6_0)),X1) = X1
    | X2 != k2_relat_1(esk6_0)
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_43]),c_0_21]),c_0_22])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk7_0,esk5_0)
    | k1_relat_1(esk6_0) != esk5_0
    | esk6_0 != k6_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_48,negated_conjecture,
    ( k1_funct_1(esk6_0,esk7_0) != esk7_0
    | k1_relat_1(esk6_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])])).

cnf(c_0_49,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( k1_funct_1(k6_relat_1(k2_relat_1(esk6_0)),esk7_0) = esk7_0
    | k2_relat_1(esk6_0) != esk5_0
    | k6_relat_1(esk5_0) != esk6_0
    | k1_relat_1(esk6_0) != esk5_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( k1_funct_1(esk6_0,esk7_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49])])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_45])]),c_0_51]),c_0_45]),c_0_51]),c_0_49])]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:57:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 1.03/1.19  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 1.03/1.19  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.03/1.19  #
% 1.03/1.19  # Preprocessing time       : 0.029 s
% 1.03/1.19  # Presaturation interreduction done
% 1.03/1.19  
% 1.03/1.19  # Proof found!
% 1.03/1.19  # SZS status Theorem
% 1.03/1.19  # SZS output start CNFRefutation
% 1.03/1.19  fof(t34_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k6_relat_1(X1)<=>(k1_relat_1(X2)=X1&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 1.03/1.19  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 1.03/1.19  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.03/1.19  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.03/1.19  fof(t23_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(X2))=>k1_funct_1(k5_relat_1(X2,X3),X1)=k1_funct_1(X3,k1_funct_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 1.03/1.19  fof(t78_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 1.03/1.19  fof(t9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k1_relat_1(X1)=k1_relat_1(X2)&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 1.03/1.19  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 1.03/1.19  fof(c_0_8, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k6_relat_1(X1)<=>(k1_relat_1(X2)=X1&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=X3))))), inference(assume_negation,[status(cth)],[t34_funct_1])).
% 1.03/1.19  fof(c_0_9, plain, ![X8, X9, X10, X12, X13, X14, X16]:((((r2_hidden(esk1_3(X8,X9,X10),k1_relat_1(X8))|~r2_hidden(X10,X9)|X9!=k2_relat_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8)))&(X10=k1_funct_1(X8,esk1_3(X8,X9,X10))|~r2_hidden(X10,X9)|X9!=k2_relat_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8))))&(~r2_hidden(X13,k1_relat_1(X8))|X12!=k1_funct_1(X8,X13)|r2_hidden(X12,X9)|X9!=k2_relat_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8))))&((~r2_hidden(esk2_2(X8,X14),X14)|(~r2_hidden(X16,k1_relat_1(X8))|esk2_2(X8,X14)!=k1_funct_1(X8,X16))|X14=k2_relat_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8)))&((r2_hidden(esk3_2(X8,X14),k1_relat_1(X8))|r2_hidden(esk2_2(X8,X14),X14)|X14=k2_relat_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8)))&(esk2_2(X8,X14)=k1_funct_1(X8,esk3_2(X8,X14))|r2_hidden(esk2_2(X8,X14),X14)|X14=k2_relat_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 1.03/1.19  fof(c_0_10, plain, ![X5]:(k1_relat_1(k6_relat_1(X5))=X5&k2_relat_1(k6_relat_1(X5))=X5), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 1.03/1.19  fof(c_0_11, plain, ![X18]:(v1_relat_1(k6_relat_1(X18))&v1_funct_1(k6_relat_1(X18))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 1.03/1.19  fof(c_0_12, negated_conjecture, ![X31]:((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&(((r2_hidden(esk7_0,esk5_0)|k1_relat_1(esk6_0)!=esk5_0|esk6_0!=k6_relat_1(esk5_0))&(k1_funct_1(esk6_0,esk7_0)!=esk7_0|k1_relat_1(esk6_0)!=esk5_0|esk6_0!=k6_relat_1(esk5_0)))&((k1_relat_1(esk6_0)=esk5_0|esk6_0=k6_relat_1(esk5_0))&(~r2_hidden(X31,esk5_0)|k1_funct_1(esk6_0,X31)=X31|esk6_0=k6_relat_1(esk5_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])).
% 1.03/1.19  fof(c_0_13, plain, ![X22, X23, X24]:(~v1_relat_1(X23)|~v1_funct_1(X23)|(~v1_relat_1(X24)|~v1_funct_1(X24)|(~r2_hidden(X22,k1_relat_1(X23))|k1_funct_1(k5_relat_1(X23,X24),X22)=k1_funct_1(X24,k1_funct_1(X23,X22))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).
% 1.03/1.19  cnf(c_0_14, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.03/1.19  cnf(c_0_15, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.03/1.19  cnf(c_0_16, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.03/1.19  cnf(c_0_17, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.03/1.19  cnf(c_0_18, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.03/1.19  cnf(c_0_19, negated_conjecture, (k1_funct_1(esk6_0,X1)=X1|esk6_0=k6_relat_1(esk5_0)|~r2_hidden(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.03/1.19  cnf(c_0_20, plain, (k1_funct_1(k5_relat_1(X1,X2),X3)=k1_funct_1(X2,k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.03/1.19  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.03/1.19  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.03/1.19  cnf(c_0_23, plain, (r2_hidden(X1,X2)|X1!=k1_funct_1(k6_relat_1(X2),X3)|~r2_hidden(X3,X2)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17]), c_0_18])])])).
% 1.03/1.19  fof(c_0_24, plain, ![X6]:(~v1_relat_1(X6)|k5_relat_1(k6_relat_1(k1_relat_1(X6)),X6)=X6), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).
% 1.03/1.19  cnf(c_0_25, negated_conjecture, (k1_funct_1(k5_relat_1(X1,esk6_0),X2)=k1_funct_1(X1,X2)|k6_relat_1(esk5_0)=esk6_0|~r2_hidden(k1_funct_1(X1,X2),esk5_0)|~r2_hidden(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])])).
% 1.03/1.19  cnf(c_0_26, plain, (r2_hidden(k1_funct_1(k6_relat_1(X1),X2),X1)|~r2_hidden(X2,X1)), inference(er,[status(thm)],[c_0_23])).
% 1.03/1.19  cnf(c_0_27, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.03/1.19  cnf(c_0_28, negated_conjecture, (k1_relat_1(esk6_0)=esk5_0|esk6_0=k6_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.03/1.19  fof(c_0_29, plain, ![X25, X26]:((r2_hidden(esk4_2(X25,X26),k1_relat_1(X25))|k1_relat_1(X25)!=k1_relat_1(X26)|X25=X26|(~v1_relat_1(X26)|~v1_funct_1(X26))|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(k1_funct_1(X25,esk4_2(X25,X26))!=k1_funct_1(X26,esk4_2(X25,X26))|k1_relat_1(X25)!=k1_relat_1(X26)|X25=X26|(~v1_relat_1(X26)|~v1_funct_1(X26))|(~v1_relat_1(X25)|~v1_funct_1(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).
% 1.03/1.19  fof(c_0_30, plain, ![X7]:(~v1_relat_1(X7)|k5_relat_1(X7,k6_relat_1(k2_relat_1(X7)))=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 1.03/1.19  cnf(c_0_31, negated_conjecture, (k1_funct_1(k5_relat_1(k6_relat_1(esk5_0),esk6_0),X1)=k1_funct_1(k6_relat_1(esk5_0),X1)|k6_relat_1(esk5_0)=esk6_0|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_15]), c_0_17]), c_0_18])])).
% 1.03/1.19  cnf(c_0_32, negated_conjecture, (k5_relat_1(k6_relat_1(esk5_0),esk6_0)=esk6_0|k6_relat_1(esk5_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_22])])).
% 1.03/1.19  cnf(c_0_33, plain, (r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))|X1=X2|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.03/1.19  cnf(c_0_34, plain, (X1=k1_funct_1(X2,esk1_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.03/1.19  cnf(c_0_35, plain, (r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.03/1.19  cnf(c_0_36, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.03/1.19  cnf(c_0_37, plain, (X1=X2|k1_funct_1(X1,esk4_2(X1,X2))!=k1_funct_1(X2,esk4_2(X1,X2))|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.03/1.19  cnf(c_0_38, negated_conjecture, (k1_funct_1(k6_relat_1(esk5_0),X1)=k1_funct_1(esk6_0,X1)|k6_relat_1(esk5_0)=esk6_0|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 1.03/1.19  cnf(c_0_39, plain, (k6_relat_1(X1)=X2|r2_hidden(esk4_2(k6_relat_1(X1),X2),X1)|X1!=k1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_15]), c_0_17]), c_0_18])])).
% 1.03/1.19  cnf(c_0_40, plain, (k1_funct_1(k5_relat_1(X1,X2),esk1_3(X1,X3,X4))=k1_funct_1(X2,X4)|X3!=k2_relat_1(X1)|~r2_hidden(X4,X3)|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_34]), c_0_35])).
% 1.03/1.19  cnf(c_0_41, negated_conjecture, (k5_relat_1(esk6_0,k6_relat_1(k2_relat_1(esk6_0)))=esk6_0), inference(spm,[status(thm)],[c_0_36, c_0_22])).
% 1.03/1.19  cnf(c_0_42, negated_conjecture, (k6_relat_1(esk5_0)=esk6_0|k6_relat_1(esk5_0)=X1|k1_funct_1(esk6_0,esk4_2(k6_relat_1(esk5_0),X1))!=k1_funct_1(X1,esk4_2(k6_relat_1(esk5_0),X1))|k1_relat_1(X1)!=esk5_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_15]), c_0_17]), c_0_18])]), c_0_39])).
% 1.03/1.19  cnf(c_0_43, negated_conjecture, (k1_funct_1(esk6_0,esk1_3(esk6_0,X1,X2))=k1_funct_1(k6_relat_1(k2_relat_1(esk6_0)),X2)|X1!=k2_relat_1(esk6_0)|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_17]), c_0_21]), c_0_18]), c_0_22])])).
% 1.03/1.19  cnf(c_0_44, negated_conjecture, (k1_funct_1(esk6_0,esk7_0)!=esk7_0|k1_relat_1(esk6_0)!=esk5_0|esk6_0!=k6_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.03/1.19  cnf(c_0_45, negated_conjecture, (k6_relat_1(esk5_0)=esk6_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_42]), c_0_21]), c_0_22])]), c_0_28])).
% 1.03/1.19  cnf(c_0_46, negated_conjecture, (k1_funct_1(k6_relat_1(k2_relat_1(esk6_0)),X1)=X1|X2!=k2_relat_1(esk6_0)|~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_43]), c_0_21]), c_0_22])])).
% 1.03/1.19  cnf(c_0_47, negated_conjecture, (r2_hidden(esk7_0,esk5_0)|k1_relat_1(esk6_0)!=esk5_0|esk6_0!=k6_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.03/1.19  cnf(c_0_48, negated_conjecture, (k1_funct_1(esk6_0,esk7_0)!=esk7_0|k1_relat_1(esk6_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45])])).
% 1.03/1.19  cnf(c_0_49, negated_conjecture, (k1_relat_1(esk6_0)=esk5_0), inference(spm,[status(thm)],[c_0_15, c_0_45])).
% 1.03/1.19  cnf(c_0_50, negated_conjecture, (k1_funct_1(k6_relat_1(k2_relat_1(esk6_0)),esk7_0)=esk7_0|k2_relat_1(esk6_0)!=esk5_0|k6_relat_1(esk5_0)!=esk6_0|k1_relat_1(esk6_0)!=esk5_0), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 1.03/1.19  cnf(c_0_51, negated_conjecture, (k2_relat_1(esk6_0)=esk5_0), inference(spm,[status(thm)],[c_0_16, c_0_45])).
% 1.03/1.19  cnf(c_0_52, negated_conjecture, (k1_funct_1(esk6_0,esk7_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49])])).
% 1.03/1.19  cnf(c_0_53, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_45])]), c_0_51]), c_0_45]), c_0_51]), c_0_49])]), c_0_52]), ['proof']).
% 1.03/1.19  # SZS output end CNFRefutation
% 1.03/1.19  # Proof object total steps             : 54
% 1.03/1.19  # Proof object clause steps            : 37
% 1.03/1.19  # Proof object formula steps           : 17
% 1.03/1.19  # Proof object conjectures             : 24
% 1.03/1.19  # Proof object clause conjectures      : 21
% 1.03/1.19  # Proof object formula conjectures     : 3
% 1.03/1.19  # Proof object initial clauses used    : 18
% 1.03/1.19  # Proof object initial formulas used   : 8
% 1.03/1.19  # Proof object generating inferences   : 16
% 1.03/1.19  # Proof object simplifying inferences  : 47
% 1.03/1.19  # Training examples: 0 positive, 0 negative
% 1.03/1.19  # Parsed axioms                        : 9
% 1.03/1.19  # Removed by relevancy pruning/SinE    : 0
% 1.03/1.19  # Initial clauses                      : 24
% 1.03/1.19  # Removed in clause preprocessing      : 0
% 1.03/1.19  # Initial clauses in saturation        : 24
% 1.03/1.19  # Processed clauses                    : 4050
% 1.03/1.19  # ...of these trivial                  : 64
% 1.03/1.19  # ...subsumed                          : 3139
% 1.03/1.19  # ...remaining for further processing  : 846
% 1.03/1.19  # Other redundant clauses eliminated   : 304
% 1.03/1.19  # Clauses deleted for lack of memory   : 0
% 1.03/1.19  # Backward-subsumed                    : 17
% 1.03/1.19  # Backward-rewritten                   : 675
% 1.03/1.19  # Generated clauses                    : 58545
% 1.03/1.19  # ...of the previous two non-trivial   : 56938
% 1.03/1.19  # Contextual simplify-reflections      : 45
% 1.03/1.19  # Paramodulations                      : 58160
% 1.03/1.19  # Factorizations                       : 0
% 1.03/1.19  # Equation resolutions                 : 385
% 1.03/1.19  # Propositional unsat checks           : 0
% 1.03/1.19  #    Propositional check models        : 0
% 1.03/1.19  #    Propositional check unsatisfiable : 0
% 1.03/1.19  #    Propositional clauses             : 0
% 1.03/1.19  #    Propositional clauses after purity: 0
% 1.03/1.19  #    Propositional unsat core size     : 0
% 1.03/1.19  #    Propositional preprocessing time  : 0.000
% 1.03/1.19  #    Propositional encoding time       : 0.000
% 1.03/1.19  #    Propositional solver time         : 0.000
% 1.03/1.19  #    Success case prop preproc time    : 0.000
% 1.03/1.19  #    Success case prop encoding time   : 0.000
% 1.03/1.19  #    Success case prop solver time     : 0.000
% 1.03/1.19  # Current number of processed clauses  : 130
% 1.03/1.19  #    Positive orientable unit clauses  : 12
% 1.03/1.19  #    Positive unorientable unit clauses: 0
% 1.03/1.19  #    Negative unit clauses             : 1
% 1.03/1.19  #    Non-unit-clauses                  : 117
% 1.03/1.19  # Current number of unprocessed clauses: 52910
% 1.03/1.19  # ...number of literals in the above   : 398679
% 1.03/1.19  # Current number of archived formulas  : 0
% 1.03/1.19  # Current number of archived clauses   : 716
% 1.03/1.19  # Clause-clause subsumption calls (NU) : 144775
% 1.03/1.19  # Rec. Clause-clause subsumption calls : 84773
% 1.03/1.19  # Non-unit clause-clause subsumptions  : 3201
% 1.03/1.19  # Unit Clause-clause subsumption calls : 27
% 1.03/1.19  # Rewrite failures with RHS unbound    : 0
% 1.03/1.19  # BW rewrite match attempts            : 3
% 1.03/1.19  # BW rewrite match successes           : 3
% 1.03/1.19  # Condensation attempts                : 0
% 1.03/1.19  # Condensation successes               : 0
% 1.03/1.19  # Termbank termtop insertions          : 1781606
% 1.03/1.19  
% 1.03/1.19  # -------------------------------------------------
% 1.03/1.19  # User time                : 0.820 s
% 1.03/1.19  # System time              : 0.031 s
% 1.03/1.19  # Total time               : 0.851 s
% 1.03/1.19  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
