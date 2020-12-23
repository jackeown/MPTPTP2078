%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:18 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   57 (7708 expanded)
%              Number of clauses        :   46 (3093 expanded)
%              Number of leaves         :    5 (1799 expanded)
%              Depth                    :   21
%              Number of atoms          :  193 (47272 expanded)
%              Number of equality atoms :   87 (22495 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(d10_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k6_relat_1(X1)
      <=> ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X2)
          <=> ( r2_hidden(X3,X1)
              & X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( X2 = k6_relat_1(X1)
        <=> ( k1_relat_1(X2) = X1
            & ! [X3] :
                ( r2_hidden(X3,X1)
               => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_funct_1])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( r2_hidden(X7,X5)
        | ~ r2_hidden(k4_tarski(X7,X8),X6)
        | X6 != k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( X7 = X8
        | ~ r2_hidden(k4_tarski(X7,X8),X6)
        | X6 != k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(X9,X5)
        | X9 != X10
        | r2_hidden(k4_tarski(X9,X10),X6)
        | X6 != k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | ~ r2_hidden(esk1_2(X5,X6),X5)
        | esk1_2(X5,X6) != esk2_2(X5,X6)
        | X6 = k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_2(X5,X6),X5)
        | r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | X6 = k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( esk1_2(X5,X6) = esk2_2(X5,X6)
        | r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | X6 = k6_relat_1(X5)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).

fof(c_0_7,negated_conjecture,(
    ! [X21] :
      ( v1_relat_1(esk4_0)
      & v1_funct_1(esk4_0)
      & ( r2_hidden(esk5_0,esk3_0)
        | k1_relat_1(esk4_0) != esk3_0
        | esk4_0 != k6_relat_1(esk3_0) )
      & ( k1_funct_1(esk4_0,esk5_0) != esk5_0
        | k1_relat_1(esk4_0) != esk3_0
        | esk4_0 != k6_relat_1(esk3_0) )
      & ( k1_relat_1(esk4_0) = esk3_0
        | esk4_0 = k6_relat_1(esk3_0) )
      & ( ~ r2_hidden(X21,esk3_0)
        | k1_funct_1(esk4_0,X21) = X21
        | esk4_0 = k6_relat_1(esk3_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).

fof(c_0_8,plain,(
    ! [X15,X16,X17] :
      ( ( r2_hidden(X15,k1_relat_1(X17))
        | ~ r2_hidden(k4_tarski(X15,X16),X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( X16 = k1_funct_1(X17,X15)
        | ~ r2_hidden(k4_tarski(X15,X16),X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( ~ r2_hidden(X15,k1_relat_1(X17))
        | X16 != k1_funct_1(X17,X15)
        | r2_hidden(k4_tarski(X15,X16),X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_9,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | X2 = k6_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( k6_relat_1(X1) = esk4_0
    | r2_hidden(k4_tarski(esk1_2(X1,esk4_0),esk2_2(X1,esk4_0)),esk4_0)
    | r2_hidden(esk1_2(X1,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_14,plain,(
    ! [X14] :
      ( v1_relat_1(k6_relat_1(X14))
      & v1_funct_1(k6_relat_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_15,negated_conjecture,
    ( k6_relat_1(X1) = esk4_0
    | r2_hidden(esk1_2(X1,esk4_0),k1_relat_1(esk4_0))
    | r2_hidden(esk1_2(X1,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_10])])).

cnf(c_0_16,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk3_0
    | esk4_0 = k6_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2)
    | X1 != X3
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X13] :
      ( k1_relat_1(k6_relat_1(X13)) = X13
      & k2_relat_1(k6_relat_1(X13)) = X13 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_20,negated_conjecture,
    ( k6_relat_1(esk3_0) = esk4_0
    | k6_relat_1(X1) = esk4_0
    | r2_hidden(esk1_2(X1,esk4_0),esk3_0)
    | r2_hidden(esk1_2(X1,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X1,X1),k6_relat_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_17])]),c_0_18])])).

cnf(c_0_23,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( k6_relat_1(esk3_0) = esk4_0
    | r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0) ),
    inference(ef,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k1_funct_1(k6_relat_1(X1),X2) = X2
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_18])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0)
    | k1_relat_1(esk4_0) != esk3_0
    | esk4_0 != k6_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk3_0
    | r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = X1
    | r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)
    | r2_hidden(esk5_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k1_funct_1(esk4_0,esk5_0) != esk5_0
    | k1_relat_1(esk4_0) != esk3_0
    | esk4_0 != k6_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_32,negated_conjecture,
    ( k1_funct_1(esk4_0,esk5_0) = esk5_0
    | r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,plain,
    ( esk1_2(X1,X2) = esk2_2(X1,X2)
    | r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | X2 = k6_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = X1
    | esk4_0 = k6_relat_1(esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_28]),c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( esk2_2(X1,esk4_0) = esk1_2(X1,esk4_0)
    | k6_relat_1(X1) = esk4_0
    | r2_hidden(k4_tarski(esk1_2(X1,esk4_0),esk2_2(X1,esk4_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_10])).

cnf(c_0_37,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_2(esk3_0,esk4_0)) = esk1_2(esk3_0,esk4_0)
    | k6_relat_1(esk3_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_2(X1,esk4_0)) = esk2_2(X1,esk4_0)
    | esk2_2(X1,esk4_0) = esk1_2(X1,esk4_0)
    | k6_relat_1(X1) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_36]),c_0_13]),c_0_10])])).

cnf(c_0_39,negated_conjecture,
    ( esk2_2(esk3_0,esk4_0) = esk1_2(esk3_0,esk4_0)
    | k6_relat_1(esk3_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_40,negated_conjecture,
    ( esk2_2(esk3_0,esk4_0) = esk1_2(esk3_0,esk4_0)
    | k1_relat_1(esk4_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_39])).

cnf(c_0_41,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_42,negated_conjecture,
    ( esk2_2(esk3_0,esk4_0) = esk1_2(esk3_0,esk4_0)
    | k1_funct_1(esk4_0,X1) = X1
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( esk2_2(esk3_0,esk4_0) = esk1_2(esk3_0,esk4_0)
    | r2_hidden(esk5_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_40]),c_0_39])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( esk2_2(esk3_0,esk4_0) = esk1_2(esk3_0,esk4_0)
    | k1_funct_1(esk4_0,esk5_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( k6_relat_1(esk3_0) = esk4_0
    | r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),esk1_2(esk3_0,esk4_0)),esk4_0)
    | ~ r2_hidden(esk1_2(esk3_0,esk4_0),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_37]),c_0_13]),c_0_10])])).

cnf(c_0_47,plain,
    ( X2 = k6_relat_1(X1)
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | ~ r2_hidden(esk1_2(X1,X2),X1)
    | esk1_2(X1,X2) != esk2_2(X1,X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_48,negated_conjecture,
    ( esk2_2(esk3_0,esk4_0) = esk1_2(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_45]),c_0_40]),c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( k6_relat_1(esk3_0) = esk4_0
    | r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),esk1_2(esk3_0,esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_16]),c_0_35])])).

cnf(c_0_50,negated_conjecture,
    ( k6_relat_1(esk3_0) = esk4_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_35]),c_0_10])]),c_0_49])).

cnf(c_0_51,negated_conjecture,
    ( k1_funct_1(esk4_0,esk5_0) != esk5_0
    | k1_relat_1(esk4_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_50])])).

cnf(c_0_52,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( k1_funct_1(esk4_0,esk5_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52])])).

cnf(c_0_54,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = X1
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_50])]),c_0_52])])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:07:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.39  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.39  #
% 0.18/0.39  # Preprocessing time       : 0.027 s
% 0.18/0.39  # Presaturation interreduction done
% 0.18/0.39  
% 0.18/0.39  # Proof found!
% 0.18/0.39  # SZS status Theorem
% 0.18/0.39  # SZS output start CNFRefutation
% 0.18/0.39  fof(t34_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k6_relat_1(X1)<=>(k1_relat_1(X2)=X1&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 0.18/0.39  fof(d10_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k6_relat_1(X1)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X2)<=>(r2_hidden(X3,X1)&X3=X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_relat_1)).
% 0.18/0.39  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.18/0.39  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.18/0.39  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.18/0.39  fof(c_0_5, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k6_relat_1(X1)<=>(k1_relat_1(X2)=X1&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=X3))))), inference(assume_negation,[status(cth)],[t34_funct_1])).
% 0.18/0.39  fof(c_0_6, plain, ![X5, X6, X7, X8, X9, X10]:((((r2_hidden(X7,X5)|~r2_hidden(k4_tarski(X7,X8),X6)|X6!=k6_relat_1(X5)|~v1_relat_1(X6))&(X7=X8|~r2_hidden(k4_tarski(X7,X8),X6)|X6!=k6_relat_1(X5)|~v1_relat_1(X6)))&(~r2_hidden(X9,X5)|X9!=X10|r2_hidden(k4_tarski(X9,X10),X6)|X6!=k6_relat_1(X5)|~v1_relat_1(X6)))&((~r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)|(~r2_hidden(esk1_2(X5,X6),X5)|esk1_2(X5,X6)!=esk2_2(X5,X6))|X6=k6_relat_1(X5)|~v1_relat_1(X6))&((r2_hidden(esk1_2(X5,X6),X5)|r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)|X6=k6_relat_1(X5)|~v1_relat_1(X6))&(esk1_2(X5,X6)=esk2_2(X5,X6)|r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)|X6=k6_relat_1(X5)|~v1_relat_1(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).
% 0.18/0.39  fof(c_0_7, negated_conjecture, ![X21]:((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&(((r2_hidden(esk5_0,esk3_0)|k1_relat_1(esk4_0)!=esk3_0|esk4_0!=k6_relat_1(esk3_0))&(k1_funct_1(esk4_0,esk5_0)!=esk5_0|k1_relat_1(esk4_0)!=esk3_0|esk4_0!=k6_relat_1(esk3_0)))&((k1_relat_1(esk4_0)=esk3_0|esk4_0=k6_relat_1(esk3_0))&(~r2_hidden(X21,esk3_0)|k1_funct_1(esk4_0,X21)=X21|esk4_0=k6_relat_1(esk3_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).
% 0.18/0.39  fof(c_0_8, plain, ![X15, X16, X17]:(((r2_hidden(X15,k1_relat_1(X17))|~r2_hidden(k4_tarski(X15,X16),X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(X16=k1_funct_1(X17,X15)|~r2_hidden(k4_tarski(X15,X16),X17)|(~v1_relat_1(X17)|~v1_funct_1(X17))))&(~r2_hidden(X15,k1_relat_1(X17))|X16!=k1_funct_1(X17,X15)|r2_hidden(k4_tarski(X15,X16),X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.18/0.39  cnf(c_0_9, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)|X2=k6_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.39  cnf(c_0_10, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.39  cnf(c_0_11, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.39  cnf(c_0_12, negated_conjecture, (k6_relat_1(X1)=esk4_0|r2_hidden(k4_tarski(esk1_2(X1,esk4_0),esk2_2(X1,esk4_0)),esk4_0)|r2_hidden(esk1_2(X1,esk4_0),X1)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.18/0.39  cnf(c_0_13, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.39  fof(c_0_14, plain, ![X14]:(v1_relat_1(k6_relat_1(X14))&v1_funct_1(k6_relat_1(X14))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.18/0.39  cnf(c_0_15, negated_conjecture, (k6_relat_1(X1)=esk4_0|r2_hidden(esk1_2(X1,esk4_0),k1_relat_1(esk4_0))|r2_hidden(esk1_2(X1,esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_10])])).
% 0.18/0.39  cnf(c_0_16, negated_conjecture, (k1_relat_1(esk4_0)=esk3_0|esk4_0=k6_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.39  cnf(c_0_17, plain, (r2_hidden(k4_tarski(X1,X3),X4)|~r2_hidden(X1,X2)|X1!=X3|X4!=k6_relat_1(X2)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.39  cnf(c_0_18, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.39  fof(c_0_19, plain, ![X13]:(k1_relat_1(k6_relat_1(X13))=X13&k2_relat_1(k6_relat_1(X13))=X13), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.18/0.39  cnf(c_0_20, negated_conjecture, (k6_relat_1(esk3_0)=esk4_0|k6_relat_1(X1)=esk4_0|r2_hidden(esk1_2(X1,esk4_0),esk3_0)|r2_hidden(esk1_2(X1,esk4_0),X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.18/0.39  cnf(c_0_21, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.39  cnf(c_0_22, plain, (r2_hidden(k4_tarski(X1,X1),k6_relat_1(X2))|~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_17])]), c_0_18])])).
% 0.18/0.39  cnf(c_0_23, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.39  cnf(c_0_24, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.39  cnf(c_0_25, negated_conjecture, (k6_relat_1(esk3_0)=esk4_0|r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)), inference(ef,[status(thm)],[c_0_20])).
% 0.18/0.39  cnf(c_0_26, plain, (k1_funct_1(k6_relat_1(X1),X2)=X2|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_18])])).
% 0.18/0.39  cnf(c_0_27, negated_conjecture, (r2_hidden(esk5_0,esk3_0)|k1_relat_1(esk4_0)!=esk3_0|esk4_0!=k6_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.39  cnf(c_0_28, negated_conjecture, (k1_relat_1(esk4_0)=esk3_0|r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.39  cnf(c_0_29, negated_conjecture, (k1_funct_1(esk4_0,X1)=X1|r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_25])).
% 0.18/0.39  cnf(c_0_30, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)|r2_hidden(esk5_0,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_25])).
% 0.18/0.39  cnf(c_0_31, negated_conjecture, (k1_funct_1(esk4_0,esk5_0)!=esk5_0|k1_relat_1(esk4_0)!=esk3_0|esk4_0!=k6_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.39  cnf(c_0_32, negated_conjecture, (k1_funct_1(esk4_0,esk5_0)=esk5_0|r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.18/0.39  cnf(c_0_33, plain, (esk1_2(X1,X2)=esk2_2(X1,X2)|r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)|X2=k6_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.39  cnf(c_0_34, negated_conjecture, (k1_funct_1(esk4_0,X1)=X1|esk4_0=k6_relat_1(esk3_0)|~r2_hidden(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.39  cnf(c_0_35, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_28]), c_0_25])).
% 0.18/0.39  cnf(c_0_36, negated_conjecture, (esk2_2(X1,esk4_0)=esk1_2(X1,esk4_0)|k6_relat_1(X1)=esk4_0|r2_hidden(k4_tarski(esk1_2(X1,esk4_0),esk2_2(X1,esk4_0)),esk4_0)), inference(spm,[status(thm)],[c_0_33, c_0_10])).
% 0.18/0.39  cnf(c_0_37, negated_conjecture, (k1_funct_1(esk4_0,esk1_2(esk3_0,esk4_0))=esk1_2(esk3_0,esk4_0)|k6_relat_1(esk3_0)=esk4_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.18/0.39  cnf(c_0_38, negated_conjecture, (k1_funct_1(esk4_0,esk1_2(X1,esk4_0))=esk2_2(X1,esk4_0)|esk2_2(X1,esk4_0)=esk1_2(X1,esk4_0)|k6_relat_1(X1)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_36]), c_0_13]), c_0_10])])).
% 0.18/0.39  cnf(c_0_39, negated_conjecture, (esk2_2(esk3_0,esk4_0)=esk1_2(esk3_0,esk4_0)|k6_relat_1(esk3_0)=esk4_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.18/0.39  cnf(c_0_40, negated_conjecture, (esk2_2(esk3_0,esk4_0)=esk1_2(esk3_0,esk4_0)|k1_relat_1(esk4_0)=esk3_0), inference(spm,[status(thm)],[c_0_24, c_0_39])).
% 0.18/0.39  cnf(c_0_41, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.39  cnf(c_0_42, negated_conjecture, (esk2_2(esk3_0,esk4_0)=esk1_2(esk3_0,esk4_0)|k1_funct_1(esk4_0,X1)=X1|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_39])).
% 0.18/0.39  cnf(c_0_43, negated_conjecture, (esk2_2(esk3_0,esk4_0)=esk1_2(esk3_0,esk4_0)|r2_hidden(esk5_0,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_40]), c_0_39])).
% 0.18/0.39  cnf(c_0_44, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_41])).
% 0.18/0.39  cnf(c_0_45, negated_conjecture, (esk2_2(esk3_0,esk4_0)=esk1_2(esk3_0,esk4_0)|k1_funct_1(esk4_0,esk5_0)=esk5_0), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.18/0.39  cnf(c_0_46, negated_conjecture, (k6_relat_1(esk3_0)=esk4_0|r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),esk1_2(esk3_0,esk4_0)),esk4_0)|~r2_hidden(esk1_2(esk3_0,esk4_0),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_37]), c_0_13]), c_0_10])])).
% 0.18/0.39  cnf(c_0_47, plain, (X2=k6_relat_1(X1)|~r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)|~r2_hidden(esk1_2(X1,X2),X1)|esk1_2(X1,X2)!=esk2_2(X1,X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.39  cnf(c_0_48, negated_conjecture, (esk2_2(esk3_0,esk4_0)=esk1_2(esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_45]), c_0_40]), c_0_39])).
% 0.18/0.39  cnf(c_0_49, negated_conjecture, (k6_relat_1(esk3_0)=esk4_0|r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),esk1_2(esk3_0,esk4_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_16]), c_0_35])])).
% 0.18/0.39  cnf(c_0_50, negated_conjecture, (k6_relat_1(esk3_0)=esk4_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_35]), c_0_10])]), c_0_49])).
% 0.18/0.39  cnf(c_0_51, negated_conjecture, (k1_funct_1(esk4_0,esk5_0)!=esk5_0|k1_relat_1(esk4_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_50])])).
% 0.18/0.39  cnf(c_0_52, negated_conjecture, (k1_relat_1(esk4_0)=esk3_0), inference(spm,[status(thm)],[c_0_24, c_0_50])).
% 0.18/0.39  cnf(c_0_53, negated_conjecture, (k1_funct_1(esk4_0,esk5_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52])])).
% 0.18/0.39  cnf(c_0_54, negated_conjecture, (k1_funct_1(esk4_0,X1)=X1|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_50])).
% 0.18/0.39  cnf(c_0_55, negated_conjecture, (r2_hidden(esk5_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_50])]), c_0_52])])).
% 0.18/0.39  cnf(c_0_56, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])]), ['proof']).
% 0.18/0.39  # SZS output end CNFRefutation
% 0.18/0.39  # Proof object total steps             : 57
% 0.18/0.39  # Proof object clause steps            : 46
% 0.18/0.39  # Proof object formula steps           : 11
% 0.18/0.39  # Proof object conjectures             : 36
% 0.18/0.39  # Proof object clause conjectures      : 33
% 0.18/0.39  # Proof object formula conjectures     : 3
% 0.18/0.39  # Proof object initial clauses used    : 16
% 0.18/0.39  # Proof object initial formulas used   : 5
% 0.18/0.39  # Proof object generating inferences   : 25
% 0.18/0.39  # Proof object simplifying inferences  : 39
% 0.18/0.39  # Training examples: 0 positive, 0 negative
% 0.18/0.39  # Parsed axioms                        : 5
% 0.18/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.39  # Initial clauses                      : 19
% 0.18/0.39  # Removed in clause preprocessing      : 0
% 0.18/0.39  # Initial clauses in saturation        : 19
% 0.18/0.39  # Processed clauses                    : 145
% 0.18/0.39  # ...of these trivial                  : 0
% 0.18/0.39  # ...subsumed                          : 20
% 0.18/0.39  # ...remaining for further processing  : 125
% 0.18/0.39  # Other redundant clauses eliminated   : 9
% 0.18/0.39  # Clauses deleted for lack of memory   : 0
% 0.18/0.39  # Backward-subsumed                    : 16
% 0.18/0.39  # Backward-rewritten                   : 49
% 0.18/0.39  # Generated clauses                    : 1211
% 0.18/0.39  # ...of the previous two non-trivial   : 1113
% 0.18/0.39  # Contextual simplify-reflections      : 13
% 0.18/0.39  # Paramodulations                      : 1193
% 0.18/0.39  # Factorizations                       : 10
% 0.18/0.39  # Equation resolutions                 : 9
% 0.18/0.39  # Propositional unsat checks           : 0
% 0.18/0.39  #    Propositional check models        : 0
% 0.18/0.39  #    Propositional check unsatisfiable : 0
% 0.18/0.39  #    Propositional clauses             : 0
% 0.18/0.39  #    Propositional clauses after purity: 0
% 0.18/0.39  #    Propositional unsat core size     : 0
% 0.18/0.39  #    Propositional preprocessing time  : 0.000
% 0.18/0.39  #    Propositional encoding time       : 0.000
% 0.18/0.39  #    Propositional solver time         : 0.000
% 0.18/0.39  #    Success case prop preproc time    : 0.000
% 0.18/0.39  #    Success case prop encoding time   : 0.000
% 0.18/0.39  #    Success case prop solver time     : 0.000
% 0.18/0.39  # Current number of processed clauses  : 37
% 0.18/0.39  #    Positive orientable unit clauses  : 12
% 0.18/0.39  #    Positive unorientable unit clauses: 0
% 0.18/0.39  #    Negative unit clauses             : 1
% 0.18/0.39  #    Non-unit-clauses                  : 24
% 0.18/0.39  # Current number of unprocessed clauses: 992
% 0.18/0.39  # ...number of literals in the above   : 5667
% 0.18/0.39  # Current number of archived formulas  : 0
% 0.18/0.39  # Current number of archived clauses   : 84
% 0.18/0.39  # Clause-clause subsumption calls (NU) : 1869
% 0.18/0.39  # Rec. Clause-clause subsumption calls : 215
% 0.18/0.39  # Non-unit clause-clause subsumptions  : 35
% 0.18/0.39  # Unit Clause-clause subsumption calls : 108
% 0.18/0.39  # Rewrite failures with RHS unbound    : 0
% 0.18/0.39  # BW rewrite match attempts            : 6
% 0.18/0.39  # BW rewrite match successes           : 6
% 0.18/0.39  # Condensation attempts                : 0
% 0.18/0.39  # Condensation successes               : 0
% 0.18/0.39  # Termbank termtop insertions          : 25841
% 0.18/0.39  
% 0.18/0.39  # -------------------------------------------------
% 0.18/0.39  # User time                : 0.055 s
% 0.18/0.39  # System time              : 0.005 s
% 0.18/0.39  # Total time               : 0.060 s
% 0.18/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
