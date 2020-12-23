%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:07 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 293 expanded)
%              Number of clauses        :   45 ( 134 expanded)
%              Number of leaves         :    9 (  78 expanded)
%              Depth                    :   10
%              Number of atoms          :  177 (1051 expanded)
%              Number of equality atoms :   85 ( 458 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(t15_funct_1,axiom,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => ! [X2] :
        ? [X3] :
          ( v1_relat_1(X3)
          & v1_funct_1(X3)
          & k1_relat_1(X3) = X1
          & k2_relat_1(X3) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(s3_funct_1__e2_25__funct_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( ~ ( X1 = k1_xboole_0
              & X2 != k1_xboole_0 )
          & ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ~ ( X2 = k1_relat_1(X3)
                  & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_funct_1])).

fof(c_0_10,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X13
        | X14 != k1_tarski(X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k1_tarski(X13) )
      & ( ~ r2_hidden(esk2_2(X17,X18),X18)
        | esk2_2(X17,X18) != X17
        | X18 = k1_tarski(X17) )
      & ( r2_hidden(esk2_2(X17,X18),X18)
        | esk2_2(X17,X18) = X17
        | X18 = k1_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_11,plain,(
    ! [X21,X22,X24] :
      ( v1_relat_1(esk3_2(X21,X22))
      & v1_funct_1(esk3_2(X21,X22))
      & k1_relat_1(esk3_2(X21,X22)) = X21
      & ( ~ r2_hidden(X24,X21)
        | k1_funct_1(esk3_2(X21,X22),X24) = X22 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

fof(c_0_12,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_13,plain,(
    ! [X20] :
      ( ( k1_relat_1(X20) != k1_xboole_0
        | X20 = k1_xboole_0
        | ~ v1_relat_1(X20) )
      & ( k2_relat_1(X20) != k1_xboole_0
        | X20 = k1_xboole_0
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_14,negated_conjecture,(
    ! [X33] :
      ( ( esk6_0 != k1_xboole_0
        | esk7_0 = k1_xboole_0 )
      & ( ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33)
        | esk7_0 != k1_relat_1(X33)
        | ~ r1_tarski(k2_relat_1(X33),esk6_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_15,plain,(
    ! [X28,X29] :
      ( ( v1_relat_1(esk5_2(X28,X29))
        | X28 = k1_xboole_0 )
      & ( v1_funct_1(esk5_2(X28,X29))
        | X28 = k1_xboole_0 )
      & ( k1_relat_1(esk5_2(X28,X29)) = X28
        | X28 = k1_xboole_0 )
      & ( k2_relat_1(esk5_2(X28,X29)) = k1_tarski(X29)
        | X28 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_funct_1])])])])])).

cnf(c_0_16,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k1_funct_1(esk3_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( v1_relat_1(esk3_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( k1_relat_1(esk3_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | esk7_0 != k1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( v1_funct_1(esk5_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( v1_relat_1(esk5_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_16])).

fof(c_0_26,plain,(
    ! [X25,X27] :
      ( v1_relat_1(esk4_1(X25))
      & v1_funct_1(esk4_1(X25))
      & k1_relat_1(esk4_1(X25)) = X25
      & ( ~ r2_hidden(X27,X25)
        | k1_funct_1(esk4_1(X25),X27) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).

cnf(c_0_27,plain,
    ( v1_funct_1(esk3_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( k1_funct_1(esk3_2(X1,X2),esk1_2(X1,X3)) = X2
    | r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_29,plain,
    ( esk3_2(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_30,negated_conjecture,
    ( X1 = k1_xboole_0
    | k1_relat_1(esk5_2(X1,X2)) != esk7_0
    | ~ r1_tarski(k2_relat_1(esk5_2(X1,X2)),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_31,plain,
    ( k1_relat_1(esk5_2(X1,X2)) = X1
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,plain,
    ( esk1_2(k1_tarski(X1),X2) = X1
    | r1_tarski(k1_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_18])).

cnf(c_0_34,plain,
    ( v1_relat_1(esk4_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k1_relat_1(esk4_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk3_2(esk7_0,X1)),esk6_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_27]),c_0_21]),c_0_20])])])).

cnf(c_0_37,plain,
    ( k1_funct_1(k1_xboole_0,esk1_2(k1_xboole_0,X1)) = X2
    | r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_38,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_39,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | ~ r1_tarski(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31])])).

cnf(c_0_40,plain,
    ( k2_relat_1(esk5_2(X1,X2)) = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,plain,
    ( v1_funct_1(esk4_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_43,plain,
    ( esk4_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_34]),c_0_35])])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r1_tarski(k1_funct_1(k1_xboole_0,esk1_2(k1_xboole_0,X1)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | ~ r1_tarski(k1_tarski(X1),esk6_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_tarski(esk1_2(X1,X2)),X1)
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_18])).

cnf(c_0_48,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_50,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_43])).

cnf(c_0_51,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r1_tarski(X2,esk6_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_37])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_55,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_48]),c_0_49]),c_0_50]),c_0_51])])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | X1 = esk6_0
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_60,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_61,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_57]),c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61])]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4b
% 0.13/0.38  # and selection function SelectCQIPrecW.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t18_funct_1, conjecture, ![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 0.13/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.13/0.38  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.13/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.38  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.13/0.38  fof(t15_funct_1, axiom, ![X1]:(X1!=k1_xboole_0=>![X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&k2_relat_1(X3)=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 0.13/0.38  fof(s3_funct_1__e2_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.13/0.38  fof(c_0_9, negated_conjecture, ~(![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1))))))), inference(assume_negation,[status(cth)],[t18_funct_1])).
% 0.13/0.38  fof(c_0_10, plain, ![X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X15,X14)|X15=X13|X14!=k1_tarski(X13))&(X16!=X13|r2_hidden(X16,X14)|X14!=k1_tarski(X13)))&((~r2_hidden(esk2_2(X17,X18),X18)|esk2_2(X17,X18)!=X17|X18=k1_tarski(X17))&(r2_hidden(esk2_2(X17,X18),X18)|esk2_2(X17,X18)=X17|X18=k1_tarski(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.13/0.38  fof(c_0_11, plain, ![X21, X22, X24]:(((v1_relat_1(esk3_2(X21,X22))&v1_funct_1(esk3_2(X21,X22)))&k1_relat_1(esk3_2(X21,X22))=X21)&(~r2_hidden(X24,X21)|k1_funct_1(esk3_2(X21,X22),X24)=X22)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.13/0.38  fof(c_0_12, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.38  fof(c_0_13, plain, ![X20]:((k1_relat_1(X20)!=k1_xboole_0|X20=k1_xboole_0|~v1_relat_1(X20))&(k2_relat_1(X20)!=k1_xboole_0|X20=k1_xboole_0|~v1_relat_1(X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.13/0.38  fof(c_0_14, negated_conjecture, ![X33]:((esk6_0!=k1_xboole_0|esk7_0=k1_xboole_0)&(~v1_relat_1(X33)|~v1_funct_1(X33)|(esk7_0!=k1_relat_1(X33)|~r1_tarski(k2_relat_1(X33),esk6_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.13/0.38  fof(c_0_15, plain, ![X28, X29]:((((v1_relat_1(esk5_2(X28,X29))|X28=k1_xboole_0)&(v1_funct_1(esk5_2(X28,X29))|X28=k1_xboole_0))&(k1_relat_1(esk5_2(X28,X29))=X28|X28=k1_xboole_0))&(k2_relat_1(esk5_2(X28,X29))=k1_tarski(X29)|X28=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_funct_1])])])])])).
% 0.13/0.38  cnf(c_0_16, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_17, plain, (k1_funct_1(esk3_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_18, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_19, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_20, plain, (v1_relat_1(esk3_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_21, plain, (k1_relat_1(esk3_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (~v1_relat_1(X1)|~v1_funct_1(X1)|esk7_0!=k1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_23, plain, (v1_funct_1(esk5_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_24, plain, (v1_relat_1(esk5_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_25, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(er,[status(thm)],[c_0_16])).
% 0.13/0.38  fof(c_0_26, plain, ![X25, X27]:(((v1_relat_1(esk4_1(X25))&v1_funct_1(esk4_1(X25)))&k1_relat_1(esk4_1(X25))=X25)&(~r2_hidden(X27,X25)|k1_funct_1(esk4_1(X25),X27)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).
% 0.13/0.38  cnf(c_0_27, plain, (v1_funct_1(esk3_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_28, plain, (k1_funct_1(esk3_2(X1,X2),esk1_2(X1,X3))=X2|r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.38  cnf(c_0_29, plain, (esk3_2(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (X1=k1_xboole_0|k1_relat_1(esk5_2(X1,X2))!=esk7_0|~r1_tarski(k2_relat_1(esk5_2(X1,X2)),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.13/0.38  cnf(c_0_31, plain, (k1_relat_1(esk5_2(X1,X2))=X1|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_33, plain, (esk1_2(k1_tarski(X1),X2)=X1|r1_tarski(k1_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_25, c_0_18])).
% 0.13/0.38  cnf(c_0_34, plain, (v1_relat_1(esk4_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_35, plain, (k1_relat_1(esk4_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (~r1_tarski(k2_relat_1(esk3_2(esk7_0,X1)),esk6_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_27]), c_0_21]), c_0_20])])])).
% 0.13/0.38  cnf(c_0_37, plain, (k1_funct_1(k1_xboole_0,esk1_2(k1_xboole_0,X1))=X2|r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.38  fof(c_0_38, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (esk7_0=k1_xboole_0|~r1_tarski(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31])])).
% 0.13/0.38  cnf(c_0_40, plain, (k2_relat_1(esk5_2(X1,X2))=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_41, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.38  cnf(c_0_42, plain, (v1_funct_1(esk4_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_43, plain, (esk4_1(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_34]), c_0_35])])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (r1_tarski(k1_xboole_0,X1)|~r1_tarski(k1_funct_1(k1_xboole_0,esk1_2(k1_xboole_0,X1)),esk6_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.38  cnf(c_0_45, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (esk7_0=k1_xboole_0|~r1_tarski(k1_tarski(X1),esk6_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.38  cnf(c_0_47, plain, (r1_tarski(k1_tarski(esk1_2(X1,X2)),X1)|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_18])).
% 0.13/0.38  cnf(c_0_48, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.38  cnf(c_0_49, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.13/0.38  cnf(c_0_50, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_43])).
% 0.13/0.38  cnf(c_0_51, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (r1_tarski(k1_xboole_0,X1)|~r1_tarski(X2,esk6_0)), inference(spm,[status(thm)],[c_0_44, c_0_37])).
% 0.13/0.38  cnf(c_0_53, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_45])).
% 0.13/0.38  cnf(c_0_54, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (esk7_0=k1_xboole_0|r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (esk7_0!=k1_xboole_0|~r1_tarski(k1_xboole_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_48]), c_0_49]), c_0_50]), c_0_51])])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (esk7_0=k1_xboole_0|X1=esk6_0|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (esk7_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (esk6_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_57]), c_0_59])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61])]), c_0_59]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 63
% 0.13/0.38  # Proof object clause steps            : 45
% 0.13/0.38  # Proof object formula steps           : 18
% 0.13/0.38  # Proof object conjectures             : 18
% 0.13/0.38  # Proof object clause conjectures      : 15
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 21
% 0.13/0.38  # Proof object initial formulas used   : 9
% 0.13/0.38  # Proof object generating inferences   : 20
% 0.13/0.38  # Proof object simplifying inferences  : 22
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 9
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 28
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 28
% 0.13/0.38  # Processed clauses                    : 100
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 6
% 0.13/0.38  # ...remaining for further processing  : 94
% 0.13/0.38  # Other redundant clauses eliminated   : 15
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 4
% 0.13/0.38  # Backward-rewritten                   : 13
% 0.13/0.38  # Generated clauses                    : 194
% 0.13/0.38  # ...of the previous two non-trivial   : 181
% 0.13/0.38  # Contextual simplify-reflections      : 2
% 0.13/0.38  # Paramodulations                      : 175
% 0.13/0.38  # Factorizations                       : 3
% 0.13/0.38  # Equation resolutions                 : 15
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
% 0.13/0.38  # Current number of processed clauses  : 42
% 0.13/0.38  #    Positive orientable unit clauses  : 18
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 23
% 0.13/0.38  # Current number of unprocessed clauses: 97
% 0.13/0.38  # ...number of literals in the above   : 334
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 46
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 128
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 105
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 12
% 0.13/0.38  # Unit Clause-clause subsumption calls : 22
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 4
% 0.13/0.38  # BW rewrite match successes           : 3
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3252
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.029 s
% 0.13/0.38  # System time              : 0.008 s
% 0.13/0.38  # Total time               : 0.037 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
