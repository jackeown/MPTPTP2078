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
% DateTime   : Thu Dec  3 10:53:13 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 838 expanded)
%              Number of clauses        :   54 ( 376 expanded)
%              Number of leaves         :    6 ( 228 expanded)
%              Depth                    :   20
%              Number of atoms          :  213 (3214 expanded)
%              Number of equality atoms :   68 (1423 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(s3_funct_1__e2_24__funct_1,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( v1_relat_1(X3)
      & v1_funct_1(X3)
      & k1_relat_1(X3) = X1
      & ! [X4] :
          ( r2_hidden(X4,X1)
         => k1_funct_1(X3,X4) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(t18_funct_1,conjecture,(
    ! [X1,X2] :
      ~ ( ~ ( X1 = k1_xboole_0
            & X2 != k1_xboole_0 )
        & ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ~ ( X2 = k1_relat_1(X3)
                & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_6,plain,(
    ! [X12] :
      ( ( k1_relat_1(X12) != k1_xboole_0
        | X12 = k1_xboole_0
        | ~ v1_relat_1(X12) )
      & ( k2_relat_1(X12) != k1_xboole_0
        | X12 = k1_xboole_0
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_7,plain,(
    ! [X23,X24,X26] :
      ( v1_relat_1(esk5_2(X23,X24))
      & v1_funct_1(esk5_2(X23,X24))
      & k1_relat_1(esk5_2(X23,X24)) = X23
      & ( ~ r2_hidden(X26,X23)
        | k1_funct_1(esk5_2(X23,X24),X26) = X24 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

cnf(c_0_8,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( k1_relat_1(esk5_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( v1_relat_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k1_funct_1(esk5_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( esk5_2(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( ~ ( X1 = k1_xboole_0
              & X2 != k1_xboole_0 )
          & ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ~ ( X2 = k1_relat_1(X3)
                  & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_funct_1])).

cnf(c_0_14,plain,
    ( k1_funct_1(k1_xboole_0,X1) = X2
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,plain,
    ( v1_funct_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_16,negated_conjecture,(
    ! [X29] :
      ( ( esk6_0 != k1_xboole_0
        | esk7_0 = k1_xboole_0 )
      & ( ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29)
        | esk7_0 != k1_relat_1(X29)
        | ~ r1_tarski(k2_relat_1(X29),esk6_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).

cnf(c_0_17,plain,
    ( v1_relat_1(k1_funct_1(k1_xboole_0,X1))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_14])).

cnf(c_0_18,plain,
    ( v1_funct_1(k1_funct_1(k1_xboole_0,X1))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_14])).

fof(c_0_19,plain,(
    ! [X13,X14,X15,X17,X18,X19,X21] :
      ( ( r2_hidden(esk2_3(X13,X14,X15),k1_relat_1(X13))
        | ~ r2_hidden(X15,X14)
        | X14 != k2_relat_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( X15 = k1_funct_1(X13,esk2_3(X13,X14,X15))
        | ~ r2_hidden(X15,X14)
        | X14 != k2_relat_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( ~ r2_hidden(X18,k1_relat_1(X13))
        | X17 != k1_funct_1(X13,X18)
        | r2_hidden(X17,X14)
        | X14 != k2_relat_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( ~ r2_hidden(esk3_2(X13,X19),X19)
        | ~ r2_hidden(X21,k1_relat_1(X13))
        | esk3_2(X13,X19) != k1_funct_1(X13,X21)
        | X19 = k2_relat_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( r2_hidden(esk4_2(X13,X19),k1_relat_1(X13))
        | r2_hidden(esk3_2(X13,X19),X19)
        | X19 = k2_relat_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( esk3_2(X13,X19) = k1_funct_1(X13,esk4_2(X13,X19))
        | r2_hidden(esk3_2(X13,X19),X19)
        | X19 = k2_relat_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_20,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | esk7_0 != k1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_14])).

cnf(c_0_22,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( k1_relat_1(X1) != esk7_0
    | ~ r2_hidden(X2,k1_xboole_0)
    | ~ r1_tarski(k1_funct_1(k1_xboole_0,X2),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_14]),c_0_21]),c_0_22])).

cnf(c_0_25,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_26,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_9,c_0_12])).

cnf(c_0_27,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_12])).

cnf(c_0_28,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_12])).

cnf(c_0_29,negated_conjecture,
    ( k1_relat_1(X1) != esk7_0
    | ~ r2_hidden(X2,k1_xboole_0)
    | ~ r1_tarski(X3,esk6_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_14])).

cnf(c_0_30,plain,
    ( r2_hidden(esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),X1),k1_xboole_0)
    | ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])])).

fof(c_0_31,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_32,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(X1) != esk7_0
    | ~ r2_hidden(X2,k2_relat_1(k1_xboole_0))
    | ~ r1_tarski(X3,esk6_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_35,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_36,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_32])])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X1)
    | k1_relat_1(X2) != esk7_0
    | ~ r1_tarski(X3,esk6_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X1)
    | k1_relat_1(X2) != esk7_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | ~ r1_tarski(k2_relat_1(esk5_2(X4,X1)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_11]),c_0_15]),c_0_10]),c_0_9])])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_9])])).

cnf(c_0_44,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_45,plain,
    ( X1 = X2
    | ~ r2_hidden(X3,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_14])).

cnf(c_0_46,plain,
    ( X1 = k1_funct_1(X2,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_12]),c_0_43])])).

cnf(c_0_48,plain,
    ( X1 = k2_relat_1(k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_27]),c_0_26]),c_0_28])]),c_0_45])).

cnf(c_0_49,plain,
    ( k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_50,plain,
    ( r2_hidden(esk2_3(esk5_2(X1,X2),k2_relat_1(esk5_2(X1,X2)),X3),X1)
    | ~ r2_hidden(X3,k2_relat_1(esk5_2(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_9]),c_0_15]),c_0_10])])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_52,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_relat_1(esk5_2(X3,X2))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_49]),c_0_15]),c_0_10])]),c_0_50])).

cnf(c_0_54,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_55,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_48])).

cnf(c_0_56,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_48])).

cnf(c_0_57,plain,
    ( esk1_2(k2_relat_1(esk5_2(X1,X2)),X3) = X2
    | r1_tarski(k2_relat_1(esk5_2(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_53,c_0_34])).

cnf(c_0_58,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(X1) != esk7_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_54]),c_0_55]),c_0_56])).

cnf(c_0_59,plain,
    ( r1_tarski(k2_relat_1(esk5_2(X1,X2)),X3)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_51,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_9])])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_59]),c_0_9]),c_0_15]),c_0_10])])])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[c_0_48,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_64,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_43]),c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64])]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:00:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.42  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.027 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.20/0.42  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.20/0.42  fof(t18_funct_1, conjecture, ![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 0.20/0.42  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.20/0.42  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.42  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.42  fof(c_0_6, plain, ![X12]:((k1_relat_1(X12)!=k1_xboole_0|X12=k1_xboole_0|~v1_relat_1(X12))&(k2_relat_1(X12)!=k1_xboole_0|X12=k1_xboole_0|~v1_relat_1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.20/0.42  fof(c_0_7, plain, ![X23, X24, X26]:(((v1_relat_1(esk5_2(X23,X24))&v1_funct_1(esk5_2(X23,X24)))&k1_relat_1(esk5_2(X23,X24))=X23)&(~r2_hidden(X26,X23)|k1_funct_1(esk5_2(X23,X24),X26)=X24)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.20/0.42  cnf(c_0_8, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.42  cnf(c_0_9, plain, (k1_relat_1(esk5_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.42  cnf(c_0_10, plain, (v1_relat_1(esk5_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.42  cnf(c_0_11, plain, (k1_funct_1(esk5_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.42  cnf(c_0_12, plain, (esk5_2(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10])])])).
% 0.20/0.42  fof(c_0_13, negated_conjecture, ~(![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1))))))), inference(assume_negation,[status(cth)],[t18_funct_1])).
% 0.20/0.42  cnf(c_0_14, plain, (k1_funct_1(k1_xboole_0,X1)=X2|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.42  cnf(c_0_15, plain, (v1_funct_1(esk5_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.42  fof(c_0_16, negated_conjecture, ![X29]:((esk6_0!=k1_xboole_0|esk7_0=k1_xboole_0)&(~v1_relat_1(X29)|~v1_funct_1(X29)|(esk7_0!=k1_relat_1(X29)|~r1_tarski(k2_relat_1(X29),esk6_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).
% 0.20/0.42  cnf(c_0_17, plain, (v1_relat_1(k1_funct_1(k1_xboole_0,X1))|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_10, c_0_14])).
% 0.20/0.42  cnf(c_0_18, plain, (v1_funct_1(k1_funct_1(k1_xboole_0,X1))|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_15, c_0_14])).
% 0.20/0.42  fof(c_0_19, plain, ![X13, X14, X15, X17, X18, X19, X21]:((((r2_hidden(esk2_3(X13,X14,X15),k1_relat_1(X13))|~r2_hidden(X15,X14)|X14!=k2_relat_1(X13)|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(X15=k1_funct_1(X13,esk2_3(X13,X14,X15))|~r2_hidden(X15,X14)|X14!=k2_relat_1(X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))))&(~r2_hidden(X18,k1_relat_1(X13))|X17!=k1_funct_1(X13,X18)|r2_hidden(X17,X14)|X14!=k2_relat_1(X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))))&((~r2_hidden(esk3_2(X13,X19),X19)|(~r2_hidden(X21,k1_relat_1(X13))|esk3_2(X13,X19)!=k1_funct_1(X13,X21))|X19=k2_relat_1(X13)|(~v1_relat_1(X13)|~v1_funct_1(X13)))&((r2_hidden(esk4_2(X13,X19),k1_relat_1(X13))|r2_hidden(esk3_2(X13,X19),X19)|X19=k2_relat_1(X13)|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(esk3_2(X13,X19)=k1_funct_1(X13,esk4_2(X13,X19))|r2_hidden(esk3_2(X13,X19),X19)|X19=k2_relat_1(X13)|(~v1_relat_1(X13)|~v1_funct_1(X13)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.20/0.42  cnf(c_0_20, negated_conjecture, (~v1_relat_1(X1)|~v1_funct_1(X1)|esk7_0!=k1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_21, plain, (v1_relat_1(X1)|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_17, c_0_14])).
% 0.20/0.42  cnf(c_0_22, plain, (v1_funct_1(X1)|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_18, c_0_14])).
% 0.20/0.42  cnf(c_0_23, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_24, negated_conjecture, (k1_relat_1(X1)!=esk7_0|~r2_hidden(X2,k1_xboole_0)|~r1_tarski(k1_funct_1(k1_xboole_0,X2),esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_14]), c_0_21]), c_0_22])).
% 0.20/0.42  cnf(c_0_25, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_23])).
% 0.20/0.42  cnf(c_0_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_9, c_0_12])).
% 0.20/0.42  cnf(c_0_27, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_15, c_0_12])).
% 0.20/0.42  cnf(c_0_28, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_10, c_0_12])).
% 0.20/0.42  cnf(c_0_29, negated_conjecture, (k1_relat_1(X1)!=esk7_0|~r2_hidden(X2,k1_xboole_0)|~r1_tarski(X3,esk6_0)), inference(spm,[status(thm)],[c_0_24, c_0_14])).
% 0.20/0.42  cnf(c_0_30, plain, (r2_hidden(esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),X1),k1_xboole_0)|~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])])).
% 0.20/0.42  fof(c_0_31, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.42  cnf(c_0_32, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_33, negated_conjecture, (k1_relat_1(X1)!=esk7_0|~r2_hidden(X2,k2_relat_1(k1_xboole_0))|~r1_tarski(X3,esk6_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.42  cnf(c_0_34, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.42  fof(c_0_35, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.42  cnf(c_0_36, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.42  cnf(c_0_37, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_32])])).
% 0.20/0.42  cnf(c_0_38, negated_conjecture, (r1_tarski(k2_relat_1(k1_xboole_0),X1)|k1_relat_1(X2)!=esk7_0|~r1_tarski(X3,esk6_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.42  cnf(c_0_39, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.42  cnf(c_0_40, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.42  cnf(c_0_41, negated_conjecture, (r1_tarski(k2_relat_1(k1_xboole_0),X1)|k1_relat_1(X2)!=esk7_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.42  cnf(c_0_42, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,X4)|~r1_tarski(k2_relat_1(esk5_2(X4,X1)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_11]), c_0_15]), c_0_10]), c_0_9])])).
% 0.20/0.42  cnf(c_0_43, negated_conjecture, (r1_tarski(k2_relat_1(k1_xboole_0),X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_9])])).
% 0.20/0.42  cnf(c_0_44, plain, (r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))|r2_hidden(esk3_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_45, plain, (X1=X2|~r2_hidden(X3,k1_xboole_0)), inference(spm,[status(thm)],[c_0_14, c_0_14])).
% 0.20/0.42  cnf(c_0_46, plain, (X1=k1_funct_1(X2,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_47, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_12]), c_0_43])])).
% 0.20/0.42  cnf(c_0_48, plain, (X1=k2_relat_1(k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_27]), c_0_26]), c_0_28])]), c_0_45])).
% 0.20/0.42  cnf(c_0_49, plain, (k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_46])).
% 0.20/0.42  cnf(c_0_50, plain, (r2_hidden(esk2_3(esk5_2(X1,X2),k2_relat_1(esk5_2(X1,X2)),X3),X1)|~r2_hidden(X3,k2_relat_1(esk5_2(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_9]), c_0_15]), c_0_10])])).
% 0.20/0.42  cnf(c_0_51, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.42  cnf(c_0_52, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.42  cnf(c_0_53, plain, (X1=X2|~r2_hidden(X1,k2_relat_1(esk5_2(X3,X2)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_49]), c_0_15]), c_0_10])]), c_0_50])).
% 0.20/0.42  cnf(c_0_54, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.42  cnf(c_0_55, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0|v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_48])).
% 0.20/0.42  cnf(c_0_56, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0|v1_funct_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_48])).
% 0.20/0.42  cnf(c_0_57, plain, (esk1_2(k2_relat_1(esk5_2(X1,X2)),X3)=X2|r1_tarski(k2_relat_1(esk5_2(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_53, c_0_34])).
% 0.20/0.42  cnf(c_0_58, negated_conjecture, (k2_relat_1(k1_xboole_0)=k1_xboole_0|k1_relat_1(X1)!=esk7_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_54]), c_0_55]), c_0_56])).
% 0.20/0.42  cnf(c_0_59, plain, (r1_tarski(k2_relat_1(esk5_2(X1,X2)),X3)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_51, c_0_57])).
% 0.20/0.42  cnf(c_0_60, negated_conjecture, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_9])])).
% 0.20/0.42  cnf(c_0_61, negated_conjecture, (~r2_hidden(X1,esk6_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_59]), c_0_9]), c_0_15]), c_0_10])])])).
% 0.20/0.42  cnf(c_0_62, plain, (X1=k1_xboole_0|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[c_0_48, c_0_60])).
% 0.20/0.42  cnf(c_0_63, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_64, negated_conjecture, (esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.42  cnf(c_0_65, negated_conjecture, (esk7_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_43]), c_0_26]), c_0_27]), c_0_28])])).
% 0.20/0.42  cnf(c_0_66, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64])]), c_0_65]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 67
% 0.20/0.42  # Proof object clause steps            : 54
% 0.20/0.42  # Proof object formula steps           : 13
% 0.20/0.42  # Proof object conjectures             : 17
% 0.20/0.42  # Proof object clause conjectures      : 14
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 15
% 0.20/0.42  # Proof object initial formulas used   : 6
% 0.20/0.42  # Proof object generating inferences   : 34
% 0.20/0.42  # Proof object simplifying inferences  : 46
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 6
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 18
% 0.20/0.42  # Removed in clause preprocessing      : 0
% 0.20/0.42  # Initial clauses in saturation        : 18
% 0.20/0.42  # Processed clauses                    : 416
% 0.20/0.42  # ...of these trivial                  : 0
% 0.20/0.42  # ...subsumed                          : 235
% 0.20/0.42  # ...remaining for further processing  : 181
% 0.20/0.42  # Other redundant clauses eliminated   : 33
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 29
% 0.20/0.42  # Backward-rewritten                   : 37
% 0.20/0.42  # Generated clauses                    : 1090
% 0.20/0.42  # ...of the previous two non-trivial   : 1003
% 0.20/0.42  # Contextual simplify-reflections      : 9
% 0.20/0.42  # Paramodulations                      : 1034
% 0.20/0.42  # Factorizations                       : 24
% 0.20/0.42  # Equation resolutions                 : 33
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 94
% 0.20/0.42  #    Positive orientable unit clauses  : 11
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 2
% 0.20/0.42  #    Non-unit-clauses                  : 81
% 0.20/0.42  # Current number of unprocessed clauses: 447
% 0.20/0.42  # ...number of literals in the above   : 2074
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 84
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 3456
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 1642
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 259
% 0.20/0.42  # Unit Clause-clause subsumption calls : 145
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 10
% 0.20/0.42  # BW rewrite match successes           : 5
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 17589
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.067 s
% 0.20/0.42  # System time              : 0.004 s
% 0.20/0.42  # Total time               : 0.071 s
% 0.20/0.42  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
