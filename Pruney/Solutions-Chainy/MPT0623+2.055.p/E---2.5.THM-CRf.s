%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:13 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 670 expanded)
%              Number of clauses        :   46 ( 302 expanded)
%              Number of leaves         :    6 ( 181 expanded)
%              Depth                    :   16
%              Number of atoms          :  188 (2540 expanded)
%              Number of equality atoms :   66 (1100 expanded)
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

fof(s3_funct_1__e1_27_1__funct_1,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( v1_relat_1(X3)
      & v1_funct_1(X3)
      & k1_relat_1(X3) = X2
      & ! [X4] :
          ( r2_hidden(X4,X2)
         => k1_funct_1(X3,X4) = o_1_0_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e1_27_1__funct_1)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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

fof(c_0_6,plain,(
    ! [X11] :
      ( ( k1_relat_1(X11) != k1_xboole_0
        | X11 = k1_xboole_0
        | ~ v1_relat_1(X11) )
      & ( k2_relat_1(X11) != k1_xboole_0
        | X11 = k1_xboole_0
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_7,plain,(
    ! [X26,X27,X29] :
      ( v1_relat_1(esk6_2(X26,X27))
      & v1_funct_1(esk6_2(X26,X27))
      & k1_relat_1(esk6_2(X26,X27)) = X26
      & ( ~ r2_hidden(X29,X26)
        | k1_funct_1(esk6_2(X26,X27),X29) = X27 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

cnf(c_0_8,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( k1_relat_1(esk6_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( v1_relat_1(esk6_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k1_funct_1(esk6_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( esk6_2(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])])).

fof(c_0_13,plain,(
    ! [X22,X23,X25] :
      ( v1_relat_1(esk5_2(X22,X23))
      & v1_funct_1(esk5_2(X22,X23))
      & k1_relat_1(esk5_2(X22,X23)) = X23
      & ( ~ r2_hidden(X25,X23)
        | k1_funct_1(esk5_2(X22,X23),X25) = o_1_0_funct_1(X22) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e1_27_1__funct_1])])])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( ~ ( X1 = k1_xboole_0
              & X2 != k1_xboole_0 )
          & ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ~ ( X2 = k1_relat_1(X3)
                  & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_funct_1])).

cnf(c_0_15,plain,
    ( k1_funct_1(k1_xboole_0,X1) = X2
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_16,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_17,plain,(
    ! [X12,X13,X14,X16,X17,X18,X20] :
      ( ( r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X12))
        | ~ r2_hidden(X14,X13)
        | X13 != k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( X14 = k1_funct_1(X12,esk2_3(X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(X17,k1_relat_1(X12))
        | X16 != k1_funct_1(X12,X17)
        | r2_hidden(X16,X13)
        | X13 != k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(esk3_2(X12,X18),X18)
        | ~ r2_hidden(X20,k1_relat_1(X12))
        | esk3_2(X12,X18) != k1_funct_1(X12,X20)
        | X18 = k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(esk4_2(X12,X18),k1_relat_1(X12))
        | r2_hidden(esk3_2(X12,X18),X18)
        | X18 = k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( esk3_2(X12,X18) = k1_funct_1(X12,esk4_2(X12,X18))
        | r2_hidden(esk3_2(X12,X18),X18)
        | X18 = k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_18,plain,
    ( k1_relat_1(esk5_2(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( v1_relat_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,negated_conjecture,(
    ! [X32] :
      ( ( esk7_0 != k1_xboole_0
        | esk8_0 = k1_xboole_0 )
      & ( ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32)
        | esk8_0 != k1_relat_1(X32)
        | ~ r1_tarski(k2_relat_1(X32),esk7_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).

cnf(c_0_21,plain,
    ( X1 = X2
    | ~ r2_hidden(X3,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( esk5_2(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_18]),c_0_19])])])).

cnf(c_0_25,plain,
    ( v1_funct_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | esk8_0 != k1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( X1 = X2
    | r1_tarski(k1_xboole_0,X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_24])).

cnf(c_0_31,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_32,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X3,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_27])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_22])).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),X1),k1_xboole_0)
    | ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,plain,
    ( v1_funct_1(esk6_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r2_hidden(X3,k2_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_35])).

cnf(c_0_39,plain,
    ( X1 = k1_funct_1(X2,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_10])])).

cnf(c_0_41,plain,
    ( X1 = X2
    | r1_tarski(k2_relat_1(k1_xboole_0),X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_22])).

cnf(c_0_42,plain,
    ( k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_43,plain,
    ( r2_hidden(esk2_3(esk6_2(X1,X2),k2_relat_1(esk6_2(X1,X2)),X3),X1)
    | ~ r2_hidden(X3,k2_relat_1(esk6_2(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_9]),c_0_37]),c_0_10])])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X1)
    | r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_46,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_relat_1(esk6_2(X3,X2))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_42]),c_0_37]),c_0_10])]),c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X1) ),
    inference(ef,[status(thm)],[c_0_44])).

cnf(c_0_48,plain,
    ( X1 = k2_relat_1(k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_31]),c_0_30]),c_0_32])]),c_0_21])).

cnf(c_0_49,plain,
    ( esk1_2(k2_relat_1(esk6_2(X1,X2)),X3) = X2
    | r1_tarski(k2_relat_1(esk6_2(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_22])).

cnf(c_0_50,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_47]),c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_51,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | X1 = X2 ),
    inference(spm,[status(thm)],[c_0_21,c_0_48])).

cnf(c_0_52,plain,
    ( r1_tarski(k2_relat_1(esk6_2(X1,X2)),X3)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51])])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_52]),c_0_9]),c_0_37]),c_0_10])])])).

cnf(c_0_55,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[c_0_48,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_57,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:28:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.19/0.42  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.028 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.19/0.42  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.19/0.42  fof(s3_funct_1__e1_27_1__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X2)&![X4]:(r2_hidden(X4,X2)=>k1_funct_1(X3,X4)=o_1_0_funct_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e1_27_1__funct_1)).
% 0.19/0.42  fof(t18_funct_1, conjecture, ![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 0.19/0.42  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.42  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.19/0.42  fof(c_0_6, plain, ![X11]:((k1_relat_1(X11)!=k1_xboole_0|X11=k1_xboole_0|~v1_relat_1(X11))&(k2_relat_1(X11)!=k1_xboole_0|X11=k1_xboole_0|~v1_relat_1(X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.19/0.42  fof(c_0_7, plain, ![X26, X27, X29]:(((v1_relat_1(esk6_2(X26,X27))&v1_funct_1(esk6_2(X26,X27)))&k1_relat_1(esk6_2(X26,X27))=X26)&(~r2_hidden(X29,X26)|k1_funct_1(esk6_2(X26,X27),X29)=X27)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.19/0.42  cnf(c_0_8, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.42  cnf(c_0_9, plain, (k1_relat_1(esk6_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.42  cnf(c_0_10, plain, (v1_relat_1(esk6_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.42  cnf(c_0_11, plain, (k1_funct_1(esk6_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.42  cnf(c_0_12, plain, (esk6_2(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10])])])).
% 0.19/0.42  fof(c_0_13, plain, ![X22, X23, X25]:(((v1_relat_1(esk5_2(X22,X23))&v1_funct_1(esk5_2(X22,X23)))&k1_relat_1(esk5_2(X22,X23))=X23)&(~r2_hidden(X25,X23)|k1_funct_1(esk5_2(X22,X23),X25)=o_1_0_funct_1(X22))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e1_27_1__funct_1])])])])).
% 0.19/0.42  fof(c_0_14, negated_conjecture, ~(![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1))))))), inference(assume_negation,[status(cth)],[t18_funct_1])).
% 0.19/0.42  cnf(c_0_15, plain, (k1_funct_1(k1_xboole_0,X1)=X2|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.42  fof(c_0_16, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.42  fof(c_0_17, plain, ![X12, X13, X14, X16, X17, X18, X20]:((((r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X12))|~r2_hidden(X14,X13)|X13!=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(X14=k1_funct_1(X12,esk2_3(X12,X13,X14))|~r2_hidden(X14,X13)|X13!=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&(~r2_hidden(X17,k1_relat_1(X12))|X16!=k1_funct_1(X12,X17)|r2_hidden(X16,X13)|X13!=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&((~r2_hidden(esk3_2(X12,X18),X18)|(~r2_hidden(X20,k1_relat_1(X12))|esk3_2(X12,X18)!=k1_funct_1(X12,X20))|X18=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&((r2_hidden(esk4_2(X12,X18),k1_relat_1(X12))|r2_hidden(esk3_2(X12,X18),X18)|X18=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(esk3_2(X12,X18)=k1_funct_1(X12,esk4_2(X12,X18))|r2_hidden(esk3_2(X12,X18),X18)|X18=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.19/0.42  cnf(c_0_18, plain, (k1_relat_1(esk5_2(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  cnf(c_0_19, plain, (v1_relat_1(esk5_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  fof(c_0_20, negated_conjecture, ![X32]:((esk7_0!=k1_xboole_0|esk8_0=k1_xboole_0)&(~v1_relat_1(X32)|~v1_funct_1(X32)|(esk8_0!=k1_relat_1(X32)|~r1_tarski(k2_relat_1(X32),esk7_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).
% 0.19/0.42  cnf(c_0_21, plain, (X1=X2|~r2_hidden(X3,k1_xboole_0)), inference(spm,[status(thm)],[c_0_15, c_0_15])).
% 0.19/0.42  cnf(c_0_22, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.42  cnf(c_0_23, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  cnf(c_0_24, plain, (esk5_2(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_18]), c_0_19])])])).
% 0.19/0.42  cnf(c_0_25, plain, (v1_funct_1(esk5_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  cnf(c_0_26, negated_conjecture, (~v1_relat_1(X1)|~v1_funct_1(X1)|esk8_0!=k1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.42  cnf(c_0_27, plain, (X1=X2|r1_tarski(k1_xboole_0,X3)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.42  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.42  cnf(c_0_29, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_23])).
% 0.19/0.42  cnf(c_0_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_18, c_0_24])).
% 0.19/0.42  cnf(c_0_31, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_24])).
% 0.19/0.42  cnf(c_0_32, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_19, c_0_24])).
% 0.19/0.42  cnf(c_0_33, negated_conjecture, (r1_tarski(k1_xboole_0,X1)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r1_tarski(X3,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_27])).
% 0.19/0.42  cnf(c_0_34, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_28, c_0_22])).
% 0.19/0.42  cnf(c_0_35, plain, (r2_hidden(esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),X1),k1_xboole_0)|~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])])).
% 0.19/0.42  cnf(c_0_36, negated_conjecture, (r1_tarski(k1_xboole_0,X1)|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.42  cnf(c_0_37, plain, (v1_funct_1(esk6_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.42  cnf(c_0_38, plain, (X1=X2|~r2_hidden(X3,k2_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_21, c_0_35])).
% 0.19/0.42  cnf(c_0_39, plain, (X1=k1_funct_1(X2,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  cnf(c_0_40, negated_conjecture, (r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_10])])).
% 0.19/0.42  cnf(c_0_41, plain, (X1=X2|r1_tarski(k2_relat_1(k1_xboole_0),X3)), inference(spm,[status(thm)],[c_0_38, c_0_22])).
% 0.19/0.42  cnf(c_0_42, plain, (k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_39])).
% 0.19/0.42  cnf(c_0_43, plain, (r2_hidden(esk2_3(esk6_2(X1,X2),k2_relat_1(esk6_2(X1,X2)),X3),X1)|~r2_hidden(X3,k2_relat_1(esk6_2(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_9]), c_0_37]), c_0_10])])).
% 0.19/0.42  cnf(c_0_44, negated_conjecture, (r1_tarski(k2_relat_1(k1_xboole_0),X1)|r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.42  cnf(c_0_45, plain, (r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))|r2_hidden(esk3_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  cnf(c_0_46, plain, (X1=X2|~r2_hidden(X1,k2_relat_1(esk6_2(X3,X2)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_42]), c_0_37]), c_0_10])]), c_0_43])).
% 0.19/0.42  cnf(c_0_47, negated_conjecture, (r1_tarski(k2_relat_1(k1_xboole_0),X1)), inference(ef,[status(thm)],[c_0_44])).
% 0.19/0.42  cnf(c_0_48, plain, (X1=k2_relat_1(k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_31]), c_0_30]), c_0_32])]), c_0_21])).
% 0.19/0.42  cnf(c_0_49, plain, (esk1_2(k2_relat_1(esk6_2(X1,X2)),X3)=X2|r1_tarski(k2_relat_1(esk6_2(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_46, c_0_22])).
% 0.19/0.42  cnf(c_0_50, negated_conjecture, (esk8_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_47]), c_0_30]), c_0_31]), c_0_32])])).
% 0.19/0.42  cnf(c_0_51, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0|X1=X2), inference(spm,[status(thm)],[c_0_21, c_0_48])).
% 0.19/0.42  cnf(c_0_52, plain, (r1_tarski(k2_relat_1(esk6_2(X1,X2)),X3)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_28, c_0_49])).
% 0.19/0.42  cnf(c_0_53, negated_conjecture, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51])])).
% 0.19/0.42  cnf(c_0_54, negated_conjecture, (~r2_hidden(X1,esk7_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_52]), c_0_9]), c_0_37]), c_0_10])])])).
% 0.19/0.42  cnf(c_0_55, plain, (X1=k1_xboole_0|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[c_0_48, c_0_53])).
% 0.19/0.42  cnf(c_0_56, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.42  cnf(c_0_57, negated_conjecture, (esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.42  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])]), c_0_50]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 59
% 0.19/0.42  # Proof object clause steps            : 46
% 0.19/0.42  # Proof object formula steps           : 13
% 0.19/0.42  # Proof object conjectures             : 15
% 0.19/0.42  # Proof object clause conjectures      : 12
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 15
% 0.19/0.42  # Proof object initial formulas used   : 6
% 0.19/0.42  # Proof object generating inferences   : 27
% 0.19/0.42  # Proof object simplifying inferences  : 39
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 6
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 21
% 0.19/0.42  # Removed in clause preprocessing      : 0
% 0.19/0.42  # Initial clauses in saturation        : 21
% 0.19/0.42  # Processed clauses                    : 610
% 0.19/0.42  # ...of these trivial                  : 1
% 0.19/0.42  # ...subsumed                          : 413
% 0.19/0.42  # ...remaining for further processing  : 196
% 0.19/0.42  # Other redundant clauses eliminated   : 98
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 29
% 0.19/0.42  # Backward-rewritten                   : 23
% 0.19/0.42  # Generated clauses                    : 2461
% 0.19/0.42  # ...of the previous two non-trivial   : 2312
% 0.19/0.42  # Contextual simplify-reflections      : 8
% 0.19/0.42  # Paramodulations                      : 2330
% 0.19/0.42  # Factorizations                       : 34
% 0.19/0.42  # Equation resolutions                 : 98
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 120
% 0.19/0.42  #    Positive orientable unit clauses  : 15
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 2
% 0.19/0.42  #    Non-unit-clauses                  : 103
% 0.19/0.42  # Current number of unprocessed clauses: 1115
% 0.19/0.42  # ...number of literals in the above   : 4683
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 73
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 5115
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 3304
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 398
% 0.19/0.42  # Unit Clause-clause subsumption calls : 155
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 11
% 0.19/0.42  # BW rewrite match successes           : 8
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 30727
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.073 s
% 0.19/0.42  # System time              : 0.007 s
% 0.19/0.42  # Total time               : 0.080 s
% 0.19/0.42  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
