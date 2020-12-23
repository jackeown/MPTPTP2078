%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:19 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 166 expanded)
%              Number of clauses        :   21 (  61 expanded)
%              Number of leaves         :    6 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :  198 (1044 expanded)
%              Number of equality atoms :   22 ( 100 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   79 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t85_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( X2 = k8_relat_1(X1,X3)
          <=> ( ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                <=> ( r2_hidden(X4,k1_relat_1(X3))
                    & r2_hidden(k1_funct_1(X3,X4),X1) ) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(t86_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(k1_funct_1(X3,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_funct_1)).

fof(c_0_6,plain,(
    ! [X9,X10] :
      ( ( v1_relat_1(k5_relat_1(X9,X10))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( v1_funct_1(k5_relat_1(X9,X10))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).

fof(c_0_7,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X8)
      | k8_relat_1(X7,X8) = k5_relat_1(X8,k6_relat_1(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

fof(c_0_8,plain,(
    ! [X11] :
      ( v1_relat_1(k6_relat_1(X11))
      & v1_funct_1(k6_relat_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_9,plain,(
    ! [X12,X13,X14,X15,X16,X17] :
      ( ( r2_hidden(X15,k1_relat_1(X14))
        | ~ r2_hidden(X15,k1_relat_1(X13))
        | X13 != k8_relat_1(X12,X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( r2_hidden(k1_funct_1(X14,X15),X12)
        | ~ r2_hidden(X15,k1_relat_1(X13))
        | X13 != k8_relat_1(X12,X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( ~ r2_hidden(X16,k1_relat_1(X14))
        | ~ r2_hidden(k1_funct_1(X14,X16),X12)
        | r2_hidden(X16,k1_relat_1(X13))
        | X13 != k8_relat_1(X12,X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( ~ r2_hidden(X17,k1_relat_1(X13))
        | k1_funct_1(X13,X17) = k1_funct_1(X14,X17)
        | X13 != k8_relat_1(X12,X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X13))
        | ~ r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X13))
        | ~ r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X14))
        | ~ r2_hidden(k1_funct_1(X14,esk1_3(X12,X13,X14)),X12)
        | X13 = k8_relat_1(X12,X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( k1_funct_1(X13,esk2_3(X12,X13,X14)) != k1_funct_1(X14,esk2_3(X12,X13,X14))
        | ~ r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X13))
        | ~ r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X14))
        | ~ r2_hidden(k1_funct_1(X14,esk1_3(X12,X13,X14)),X12)
        | X13 = k8_relat_1(X12,X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X13))
        | r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X14))
        | r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X13))
        | X13 = k8_relat_1(X12,X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( k1_funct_1(X13,esk2_3(X12,X13,X14)) != k1_funct_1(X14,esk2_3(X12,X13,X14))
        | r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X14))
        | r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X13))
        | X13 = k8_relat_1(X12,X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X13))
        | r2_hidden(k1_funct_1(X14,esk1_3(X12,X13,X14)),X12)
        | r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X13))
        | X13 = k8_relat_1(X12,X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( k1_funct_1(X13,esk2_3(X12,X13,X14)) != k1_funct_1(X14,esk2_3(X12,X13,X14))
        | r2_hidden(k1_funct_1(X14,esk1_3(X12,X13,X14)),X12)
        | r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X13))
        | X13 = k8_relat_1(X12,X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_funct_1])])])])])])).

fof(c_0_10,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X6)
      | v1_relat_1(k8_relat_1(X5,X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

cnf(c_0_11,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
        <=> ( r2_hidden(X1,k1_relat_1(X3))
            & r2_hidden(k1_funct_1(X3,X1),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t86_funct_1])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | X3 != k8_relat_1(X4,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( v1_funct_1(k8_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14])])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & ( ~ r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0)))
      | ~ r2_hidden(esk3_0,k1_relat_1(esk5_0))
      | ~ r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0) )
    & ( r2_hidden(esk3_0,k1_relat_1(esk5_0))
      | r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0))) )
    & ( r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0)
      | r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,k1_relat_1(X4))
    | X4 != k8_relat_1(X3,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X4)
    | ~ v1_funct_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k8_relat_1(X3,X2)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk5_0))
    | r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,k1_relat_1(k8_relat_1(X3,X1)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_20]),c_0_17]),c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0)
    | r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0)))
    | ~ r2_hidden(esk3_0,k1_relat_1(esk5_0))
    | ~ r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_23]),c_0_24])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k1_relat_1(X4))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | X4 != k8_relat_1(X3,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_funct_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28])]),c_0_29])])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
    | ~ r2_hidden(k1_funct_1(X3,X1),X2)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_30]),c_0_17]),c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_29]),c_0_28]),c_0_23]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(fc2_funct_1, axiom, ![X1, X2]:((((v1_relat_1(X1)&v1_funct_1(X1))&v1_relat_1(X2))&v1_funct_1(X2))=>(v1_relat_1(k5_relat_1(X1,X2))&v1_funct_1(k5_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 0.13/0.38  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 0.13/0.38  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.13/0.38  fof(t85_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(X2=k8_relat_1(X1,X3)<=>(![X4]:(r2_hidden(X4,k1_relat_1(X2))<=>(r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X4),X1)))&![X4]:(r2_hidden(X4,k1_relat_1(X2))=>k1_funct_1(X2,X4)=k1_funct_1(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_funct_1)).
% 0.13/0.38  fof(dt_k8_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>v1_relat_1(k8_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 0.13/0.38  fof(t86_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_funct_1)).
% 0.13/0.38  fof(c_0_6, plain, ![X9, X10]:((v1_relat_1(k5_relat_1(X9,X10))|(~v1_relat_1(X9)|~v1_funct_1(X9)|~v1_relat_1(X10)|~v1_funct_1(X10)))&(v1_funct_1(k5_relat_1(X9,X10))|(~v1_relat_1(X9)|~v1_funct_1(X9)|~v1_relat_1(X10)|~v1_funct_1(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).
% 0.13/0.38  fof(c_0_7, plain, ![X7, X8]:(~v1_relat_1(X8)|k8_relat_1(X7,X8)=k5_relat_1(X8,k6_relat_1(X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.13/0.38  fof(c_0_8, plain, ![X11]:(v1_relat_1(k6_relat_1(X11))&v1_funct_1(k6_relat_1(X11))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.13/0.38  fof(c_0_9, plain, ![X12, X13, X14, X15, X16, X17]:(((((r2_hidden(X15,k1_relat_1(X14))|~r2_hidden(X15,k1_relat_1(X13))|X13!=k8_relat_1(X12,X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(r2_hidden(k1_funct_1(X14,X15),X12)|~r2_hidden(X15,k1_relat_1(X13))|X13!=k8_relat_1(X12,X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13))))&(~r2_hidden(X16,k1_relat_1(X14))|~r2_hidden(k1_funct_1(X14,X16),X12)|r2_hidden(X16,k1_relat_1(X13))|X13!=k8_relat_1(X12,X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13))))&(~r2_hidden(X17,k1_relat_1(X13))|k1_funct_1(X13,X17)=k1_funct_1(X14,X17)|X13!=k8_relat_1(X12,X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13))))&(((r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X13))|(~r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X13))|(~r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X14))|~r2_hidden(k1_funct_1(X14,esk1_3(X12,X13,X14)),X12)))|X13=k8_relat_1(X12,X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(k1_funct_1(X13,esk2_3(X12,X13,X14))!=k1_funct_1(X14,esk2_3(X12,X13,X14))|(~r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X13))|(~r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X14))|~r2_hidden(k1_funct_1(X14,esk1_3(X12,X13,X14)),X12)))|X13=k8_relat_1(X12,X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13))))&(((r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X13))|(r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X14))|r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X13)))|X13=k8_relat_1(X12,X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(k1_funct_1(X13,esk2_3(X12,X13,X14))!=k1_funct_1(X14,esk2_3(X12,X13,X14))|(r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X14))|r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X13)))|X13=k8_relat_1(X12,X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13))))&((r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X13))|(r2_hidden(k1_funct_1(X14,esk1_3(X12,X13,X14)),X12)|r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X13)))|X13=k8_relat_1(X12,X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(k1_funct_1(X13,esk2_3(X12,X13,X14))!=k1_funct_1(X14,esk2_3(X12,X13,X14))|(r2_hidden(k1_funct_1(X14,esk1_3(X12,X13,X14)),X12)|r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X13)))|X13=k8_relat_1(X12,X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_funct_1])])])])])])).
% 0.13/0.38  fof(c_0_10, plain, ![X5, X6]:(~v1_relat_1(X6)|v1_relat_1(k8_relat_1(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).
% 0.13/0.38  cnf(c_0_11, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_12, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_13, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_14, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),X2))))), inference(assume_negation,[status(cth)],[t86_funct_1])).
% 0.13/0.38  cnf(c_0_16, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,k1_relat_1(X3))|X3!=k8_relat_1(X4,X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_17, plain, (v1_relat_1(k8_relat_1(X2,X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_18, plain, (v1_funct_1(k8_relat_1(X1,X2))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_14])])).
% 0.13/0.38  fof(c_0_19, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&((~r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0)))|(~r2_hidden(esk3_0,k1_relat_1(esk5_0))|~r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0)))&((r2_hidden(esk3_0,k1_relat_1(esk5_0))|r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0))))&(r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0)|r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).
% 0.13/0.38  cnf(c_0_20, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~r2_hidden(X2,k1_relat_1(X4))|X4!=k8_relat_1(X3,X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X4)|~v1_funct_1(X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_21, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,k1_relat_1(k8_relat_1(X3,X2)))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_16]), c_0_17]), c_0_18])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(esk5_0))|r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_25, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~r2_hidden(X2,k1_relat_1(k8_relat_1(X3,X1)))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_20]), c_0_17]), c_0_18])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0)|r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (~r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0)))|~r2_hidden(esk3_0,k1_relat_1(esk5_0))|~r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24])])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_23]), c_0_24])])).
% 0.13/0.38  cnf(c_0_30, plain, (r2_hidden(X1,k1_relat_1(X4))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k1_funct_1(X2,X1),X3)|X4!=k8_relat_1(X3,X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X4)|~v1_funct_1(X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (~r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28])]), c_0_29])])).
% 0.13/0.38  cnf(c_0_32, plain, (r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))|~r2_hidden(k1_funct_1(X3,X1),X2)|~r2_hidden(X1,k1_relat_1(X3))|~v1_funct_1(X3)|~v1_relat_1(X3)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_30]), c_0_17]), c_0_18])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_29]), c_0_28]), c_0_23]), c_0_24])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 34
% 0.13/0.38  # Proof object clause steps            : 21
% 0.13/0.38  # Proof object formula steps           : 13
% 0.13/0.38  # Proof object conjectures             : 12
% 0.13/0.38  # Proof object clause conjectures      : 9
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 13
% 0.13/0.38  # Proof object initial formulas used   : 6
% 0.13/0.38  # Proof object generating inferences   : 4
% 0.13/0.38  # Proof object simplifying inferences  : 27
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 6
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 21
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 21
% 0.13/0.38  # Processed clauses                    : 30
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 1
% 0.13/0.38  # ...remaining for further processing  : 29
% 0.13/0.38  # Other redundant clauses eliminated   : 4
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 3
% 0.13/0.38  # Generated clauses                    : 30
% 0.13/0.38  # ...of the previous two non-trivial   : 25
% 0.13/0.38  # Contextual simplify-reflections      : 8
% 0.13/0.38  # Paramodulations                      : 25
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 5
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 22
% 0.13/0.38  #    Positive orientable unit clauses  : 6
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 15
% 0.13/0.38  # Current number of unprocessed clauses: 14
% 0.13/0.38  # ...number of literals in the above   : 118
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 3
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 352
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 23
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 9
% 0.13/0.38  # Unit Clause-clause subsumption calls : 1
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 2
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2694
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.027 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.033 s
% 0.13/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
