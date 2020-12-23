%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:20 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   28 (  45 expanded)
%              Number of clauses        :   15 (  17 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    5
%              Number of atoms          :  170 ( 221 expanded)
%              Number of equality atoms :   27 (  39 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   79 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(t87_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
       => k1_funct_1(k8_relat_1(X2,X3),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).

fof(c_0_6,plain,(
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

fof(c_0_7,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(X6)
      | v1_relat_1(k5_relat_1(X5,X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_8,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X8)
      | k8_relat_1(X7,X8) = k5_relat_1(X8,k6_relat_1(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

fof(c_0_9,plain,(
    ! [X11] :
      ( v1_relat_1(k6_relat_1(X11))
      & v1_funct_1(k6_relat_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_10,plain,(
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

cnf(c_0_11,plain,
    ( k1_funct_1(X2,X1) = k1_funct_1(X3,X1)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X2 != k8_relat_1(X4,X3)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
         => k1_funct_1(k8_relat_1(X2,X3),X1) = k1_funct_1(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t87_funct_1])).

cnf(c_0_18,plain,
    ( k1_funct_1(k8_relat_1(X1,X2),X3) = k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(k8_relat_1(X1,X2)))
    | ~ v1_funct_1(k8_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( v1_relat_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_20,plain,
    ( v1_funct_1(k8_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_13]),c_0_16]),c_0_14])])).

fof(c_0_21,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0)))
    & k1_funct_1(k8_relat_1(esk4_0,esk5_0),esk3_0) != k1_funct_1(esk5_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_22,plain,
    ( k1_funct_1(k8_relat_1(X1,X2),X3) = k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(k8_relat_1(X1,X2)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( k1_funct_1(k8_relat_1(esk4_0,esk5_0),esk3_0) != k1_funct_1(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:05:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.028 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t85_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(X2=k8_relat_1(X1,X3)<=>(![X4]:(r2_hidden(X4,k1_relat_1(X2))<=>(r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X4),X1)))&![X4]:(r2_hidden(X4,k1_relat_1(X2))=>k1_funct_1(X2,X4)=k1_funct_1(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_1)).
% 0.14/0.37  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.14/0.37  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 0.14/0.37  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.14/0.37  fof(fc2_funct_1, axiom, ![X1, X2]:((((v1_relat_1(X1)&v1_funct_1(X1))&v1_relat_1(X2))&v1_funct_1(X2))=>(v1_relat_1(k5_relat_1(X1,X2))&v1_funct_1(k5_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funct_1)).
% 0.14/0.37  fof(t87_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))=>k1_funct_1(k8_relat_1(X2,X3),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_1)).
% 0.14/0.37  fof(c_0_6, plain, ![X12, X13, X14, X15, X16, X17]:(((((r2_hidden(X15,k1_relat_1(X14))|~r2_hidden(X15,k1_relat_1(X13))|X13!=k8_relat_1(X12,X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(r2_hidden(k1_funct_1(X14,X15),X12)|~r2_hidden(X15,k1_relat_1(X13))|X13!=k8_relat_1(X12,X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13))))&(~r2_hidden(X16,k1_relat_1(X14))|~r2_hidden(k1_funct_1(X14,X16),X12)|r2_hidden(X16,k1_relat_1(X13))|X13!=k8_relat_1(X12,X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13))))&(~r2_hidden(X17,k1_relat_1(X13))|k1_funct_1(X13,X17)=k1_funct_1(X14,X17)|X13!=k8_relat_1(X12,X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13))))&(((r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X13))|(~r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X13))|(~r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X14))|~r2_hidden(k1_funct_1(X14,esk1_3(X12,X13,X14)),X12)))|X13=k8_relat_1(X12,X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(k1_funct_1(X13,esk2_3(X12,X13,X14))!=k1_funct_1(X14,esk2_3(X12,X13,X14))|(~r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X13))|(~r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X14))|~r2_hidden(k1_funct_1(X14,esk1_3(X12,X13,X14)),X12)))|X13=k8_relat_1(X12,X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13))))&(((r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X13))|(r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X14))|r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X13)))|X13=k8_relat_1(X12,X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(k1_funct_1(X13,esk2_3(X12,X13,X14))!=k1_funct_1(X14,esk2_3(X12,X13,X14))|(r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X14))|r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X13)))|X13=k8_relat_1(X12,X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13))))&((r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X13))|(r2_hidden(k1_funct_1(X14,esk1_3(X12,X13,X14)),X12)|r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X13)))|X13=k8_relat_1(X12,X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(k1_funct_1(X13,esk2_3(X12,X13,X14))!=k1_funct_1(X14,esk2_3(X12,X13,X14))|(r2_hidden(k1_funct_1(X14,esk1_3(X12,X13,X14)),X12)|r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X13)))|X13=k8_relat_1(X12,X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_funct_1])])])])])])).
% 0.14/0.37  fof(c_0_7, plain, ![X5, X6]:(~v1_relat_1(X5)|~v1_relat_1(X6)|v1_relat_1(k5_relat_1(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.14/0.37  fof(c_0_8, plain, ![X7, X8]:(~v1_relat_1(X8)|k8_relat_1(X7,X8)=k5_relat_1(X8,k6_relat_1(X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.14/0.37  fof(c_0_9, plain, ![X11]:(v1_relat_1(k6_relat_1(X11))&v1_funct_1(k6_relat_1(X11))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.14/0.37  fof(c_0_10, plain, ![X9, X10]:((v1_relat_1(k5_relat_1(X9,X10))|(~v1_relat_1(X9)|~v1_funct_1(X9)|~v1_relat_1(X10)|~v1_funct_1(X10)))&(v1_funct_1(k5_relat_1(X9,X10))|(~v1_relat_1(X9)|~v1_funct_1(X9)|~v1_relat_1(X10)|~v1_funct_1(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).
% 0.14/0.37  cnf(c_0_11, plain, (k1_funct_1(X2,X1)=k1_funct_1(X3,X1)|~r2_hidden(X1,k1_relat_1(X2))|X2!=k8_relat_1(X4,X3)|~v1_relat_1(X3)|~v1_funct_1(X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.37  cnf(c_0_12, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_13, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_14, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_15, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_16, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))=>k1_funct_1(k8_relat_1(X2,X3),X1)=k1_funct_1(X3,X1)))), inference(assume_negation,[status(cth)],[t87_funct_1])).
% 0.14/0.37  cnf(c_0_18, plain, (k1_funct_1(k8_relat_1(X1,X2),X3)=k1_funct_1(X2,X3)|~r2_hidden(X3,k1_relat_1(k8_relat_1(X1,X2)))|~v1_funct_1(k8_relat_1(X1,X2))|~v1_funct_1(X2)|~v1_relat_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_11])).
% 0.14/0.37  cnf(c_0_19, plain, (v1_relat_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])])).
% 0.14/0.37  cnf(c_0_20, plain, (v1_funct_1(k8_relat_1(X1,X2))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_13]), c_0_16]), c_0_14])])).
% 0.14/0.37  fof(c_0_21, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&(r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0)))&k1_funct_1(k8_relat_1(esk4_0,esk5_0),esk3_0)!=k1_funct_1(esk5_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.14/0.37  cnf(c_0_22, plain, (k1_funct_1(k8_relat_1(X1,X2),X3)=k1_funct_1(X2,X3)|~r2_hidden(X3,k1_relat_1(k8_relat_1(X1,X2)))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.14/0.37  cnf(c_0_23, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(k8_relat_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.37  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.37  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.37  cnf(c_0_26, negated_conjecture, (k1_funct_1(k8_relat_1(esk4_0,esk5_0),esk3_0)!=k1_funct_1(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.37  cnf(c_0_27, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])]), c_0_26]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 28
% 0.14/0.37  # Proof object clause steps            : 15
% 0.14/0.37  # Proof object formula steps           : 13
% 0.14/0.37  # Proof object conjectures             : 8
% 0.14/0.37  # Proof object clause conjectures      : 5
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 10
% 0.14/0.37  # Proof object initial formulas used   : 6
% 0.14/0.37  # Proof object generating inferences   : 3
% 0.14/0.37  # Proof object simplifying inferences  : 12
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 6
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 20
% 0.14/0.37  # Removed in clause preprocessing      : 0
% 0.14/0.37  # Initial clauses in saturation        : 20
% 0.14/0.37  # Processed clauses                    : 41
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 1
% 0.14/0.37  # ...remaining for further processing  : 40
% 0.14/0.37  # Other redundant clauses eliminated   : 4
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 1
% 0.14/0.37  # Backward-rewritten                   : 1
% 0.14/0.37  # Generated clauses                    : 11
% 0.14/0.37  # ...of the previous two non-trivial   : 10
% 0.14/0.37  # Contextual simplify-reflections      : 4
% 0.14/0.37  # Paramodulations                      : 7
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 4
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
% 0.14/0.37  # Current number of processed clauses  : 15
% 0.14/0.37  #    Positive orientable unit clauses  : 6
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 1
% 0.14/0.37  #    Non-unit-clauses                  : 8
% 0.14/0.37  # Current number of unprocessed clauses: 8
% 0.14/0.37  # ...number of literals in the above   : 58
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 21
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 289
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 26
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 6
% 0.14/0.37  # Unit Clause-clause subsumption calls : 1
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 1
% 0.14/0.37  # BW rewrite match successes           : 1
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 2200
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.032 s
% 0.14/0.37  # System time              : 0.001 s
% 0.14/0.37  # Total time               : 0.034 s
% 0.14/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
