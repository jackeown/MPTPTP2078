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
% DateTime   : Thu Dec  3 10:52:58 EST 2020

% Result     : Theorem 0.63s
% Output     : CNFRefutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 397 expanded)
%              Number of clauses        :   45 ( 178 expanded)
%              Number of leaves         :   11 ( 106 expanded)
%              Depth                    :   12
%              Number of atoms          :  240 (1741 expanded)
%              Number of equality atoms :   97 ( 698 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(t16_funct_1,conjecture,(
    ! [X1] :
      ( ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( ( k1_relat_1(X2) = X1
                  & k1_relat_1(X3) = X1 )
               => X2 = X3 ) ) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

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

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(s3_funct_1__e7_25__funct_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = np__1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

fof(t56_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),X1)
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_11,plain,(
    ! [X36,X37,X38,X40,X41,X42,X44] :
      ( ( r2_hidden(esk8_3(X36,X37,X38),k1_relat_1(X36))
        | ~ r2_hidden(X38,X37)
        | X37 != k2_relat_1(X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( X38 = k1_funct_1(X36,esk8_3(X36,X37,X38))
        | ~ r2_hidden(X38,X37)
        | X37 != k2_relat_1(X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( ~ r2_hidden(X41,k1_relat_1(X36))
        | X40 != k1_funct_1(X36,X41)
        | r2_hidden(X40,X37)
        | X37 != k2_relat_1(X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( ~ r2_hidden(esk9_2(X36,X42),X42)
        | ~ r2_hidden(X44,k1_relat_1(X36))
        | esk9_2(X36,X42) != k1_funct_1(X36,X44)
        | X42 = k2_relat_1(X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( r2_hidden(esk10_2(X36,X42),k1_relat_1(X36))
        | r2_hidden(esk9_2(X36,X42),X42)
        | X42 = k2_relat_1(X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( esk9_2(X36,X42) = k1_funct_1(X36,esk10_2(X36,X42))
        | r2_hidden(esk9_2(X36,X42),X42)
        | X42 = k2_relat_1(X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ! [X3] :
                ( ( v1_relat_1(X3)
                  & v1_funct_1(X3) )
               => ( ( k1_relat_1(X2) = X1
                    & k1_relat_1(X3) = X1 )
                 => X2 = X3 ) ) )
       => X1 = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t16_funct_1])).

fof(c_0_13,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,(
    ! [X57,X58] :
      ( ( ~ v1_relat_1(X57)
        | ~ v1_funct_1(X57)
        | ~ v1_relat_1(X58)
        | ~ v1_funct_1(X58)
        | k1_relat_1(X57) != esk14_0
        | k1_relat_1(X58) != esk14_0
        | X57 = X58 )
      & esk14_0 != k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

fof(c_0_16,plain,(
    ! [X50,X52] :
      ( v1_relat_1(esk12_1(X50))
      & v1_funct_1(esk12_1(X50))
      & k1_relat_1(esk12_1(X50)) = X50
      & ( ~ r2_hidden(X52,X50)
        | k1_funct_1(esk12_1(X50),X52) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).

fof(c_0_17,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X14,X13)
        | X14 = X11
        | X14 = X12
        | X13 != k2_tarski(X11,X12) )
      & ( X15 != X11
        | r2_hidden(X15,X13)
        | X13 != k2_tarski(X11,X12) )
      & ( X15 != X12
        | r2_hidden(X15,X13)
        | X13 != k2_tarski(X11,X12) )
      & ( esk2_3(X16,X17,X18) != X16
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_tarski(X16,X17) )
      & ( esk2_3(X16,X17,X18) != X17
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_tarski(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X18)
        | esk2_3(X16,X17,X18) = X16
        | esk2_3(X16,X17,X18) = X17
        | X18 = k2_tarski(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_18,plain,(
    ! [X20,X21] : k1_enumset1(X20,X20,X21) = k2_tarski(X20,X21) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_14])])).

fof(c_0_21,plain,(
    ! [X46,X47,X49] :
      ( v1_relat_1(esk11_2(X46,X47))
      & v1_funct_1(esk11_2(X46,X47))
      & k1_relat_1(esk11_2(X46,X47)) = X46
      & ( ~ r2_hidden(X49,X46)
        | k1_funct_1(esk11_2(X46,X47),X49) = X47 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

cnf(c_0_22,negated_conjecture,
    ( X1 = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(X1) != esk14_0
    | k1_relat_1(X2) != esk14_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k1_relat_1(esk12_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( v1_funct_1(esk12_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( v1_relat_1(esk12_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_26,plain,(
    ! [X22,X23,X24,X26,X27,X28,X29,X31] :
      ( ( ~ r2_hidden(X24,X23)
        | r2_hidden(k4_tarski(X24,esk3_3(X22,X23,X24)),X22)
        | X23 != k1_relat_1(X22) )
      & ( ~ r2_hidden(k4_tarski(X26,X27),X22)
        | r2_hidden(X26,X23)
        | X23 != k1_relat_1(X22) )
      & ( ~ r2_hidden(esk4_2(X28,X29),X29)
        | ~ r2_hidden(k4_tarski(esk4_2(X28,X29),X31),X28)
        | X29 = k1_relat_1(X28) )
      & ( r2_hidden(esk4_2(X28,X29),X29)
        | r2_hidden(k4_tarski(esk4_2(X28,X29),esk5_2(X28,X29)),X28)
        | X29 = k1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k2_relat_1(X1),k1_funct_1(X1,X2))
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_30,plain,
    ( k1_funct_1(esk11_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( v1_funct_1(esk11_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( v1_relat_1(esk11_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k1_relat_1(esk11_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( X1 = esk12_1(esk14_0)
    | k1_relat_1(X1) != esk14_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])])])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X4,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(k2_relat_1(esk11_2(X1,X2)),X2)
    | ~ r2_hidden(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_38,negated_conjecture,
    ( esk11_2(esk14_0,X1) = esk12_1(esk14_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_31]),c_0_32])])])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_36])])).

fof(c_0_41,plain,(
    ! [X53,X55] :
      ( v1_relat_1(esk13_1(X53))
      & v1_funct_1(esk13_1(X53))
      & k1_relat_1(esk13_1(X53)) = X53
      & ( ~ r2_hidden(X55,X53)
        | k1_funct_1(esk13_1(X53),X55) = np__1 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e7_25__funct_1])])])])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(k2_relat_1(esk12_1(esk14_0)),X1)
    | ~ r2_hidden(X2,esk14_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k1_relat_1(k1_enumset1(X2,X2,k4_tarski(X1,X3)))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( r2_hidden(esk8_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,plain,
    ( k1_relat_1(esk13_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( v1_funct_1(esk13_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( v1_relat_1(esk13_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(X1,esk14_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_50,plain,(
    ! [X33] :
      ( ~ v1_relat_1(X33)
      | r2_hidden(k4_tarski(esk6_1(X33),esk7_1(X33)),X33)
      | X33 = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).

cnf(c_0_51,plain,
    ( r2_hidden(esk8_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( X1 = esk13_1(esk14_0)
    | k1_relat_1(X1) != esk14_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_45]),c_0_46]),c_0_47])])])).

cnf(c_0_53,negated_conjecture,
    ( X1 = k1_relat_1(esk14_0)
    | r2_hidden(esk4_2(esk14_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( r2_hidden(k4_tarski(esk6_1(X1),esk7_1(X1)),X1)
    | X1 = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,plain,
    ( r2_hidden(esk8_3(esk13_1(X1),k2_relat_1(esk13_1(X1)),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(esk13_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_56,negated_conjecture,
    ( esk13_1(esk14_0) = esk12_1(esk14_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_23]),c_0_24]),c_0_25])])])).

cnf(c_0_57,negated_conjecture,
    ( k1_relat_1(esk14_0) = esk14_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_53])).

cnf(c_0_58,plain,
    ( esk13_1(X1) = k1_xboole_0
    | r2_hidden(k4_tarski(esk6_1(esk13_1(X1)),esk7_1(esk13_1(X1))),esk13_1(X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk12_1(esk14_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_55]),c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( X1 = esk14_0
    | r2_hidden(esk4_2(esk14_0,X1),X1) ),
    inference(rw,[status(thm)],[c_0_53,c_0_57])).

cnf(c_0_61,plain,
    ( esk13_1(X1) = k1_xboole_0
    | r2_hidden(esk6_1(esk13_1(X1)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_58]),c_0_45])).

cnf(c_0_62,negated_conjecture,
    ( k2_relat_1(esk12_1(esk14_0)) = esk14_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( esk12_1(esk14_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_61]),c_0_56])).

cnf(c_0_64,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_65,negated_conjecture,
    ( esk14_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:26:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.63/0.79  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.63/0.79  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.63/0.79  #
% 0.63/0.79  # Preprocessing time       : 0.044 s
% 0.63/0.79  # Presaturation interreduction done
% 0.63/0.79  
% 0.63/0.79  # Proof found!
% 0.63/0.79  # SZS status Theorem
% 0.63/0.79  # SZS output start CNFRefutation
% 0.63/0.79  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.63/0.79  fof(t16_funct_1, conjecture, ![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 0.63/0.79  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.63/0.79  fof(s3_funct_1__e2_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 0.63/0.79  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.63/0.79  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.63/0.79  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.63/0.79  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.63/0.79  fof(s3_funct_1__e7_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=np__1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 0.63/0.79  fof(t56_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(![X2, X3]:~(r2_hidden(k4_tarski(X2,X3),X1))=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 0.63/0.79  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.63/0.79  fof(c_0_11, plain, ![X36, X37, X38, X40, X41, X42, X44]:((((r2_hidden(esk8_3(X36,X37,X38),k1_relat_1(X36))|~r2_hidden(X38,X37)|X37!=k2_relat_1(X36)|(~v1_relat_1(X36)|~v1_funct_1(X36)))&(X38=k1_funct_1(X36,esk8_3(X36,X37,X38))|~r2_hidden(X38,X37)|X37!=k2_relat_1(X36)|(~v1_relat_1(X36)|~v1_funct_1(X36))))&(~r2_hidden(X41,k1_relat_1(X36))|X40!=k1_funct_1(X36,X41)|r2_hidden(X40,X37)|X37!=k2_relat_1(X36)|(~v1_relat_1(X36)|~v1_funct_1(X36))))&((~r2_hidden(esk9_2(X36,X42),X42)|(~r2_hidden(X44,k1_relat_1(X36))|esk9_2(X36,X42)!=k1_funct_1(X36,X44))|X42=k2_relat_1(X36)|(~v1_relat_1(X36)|~v1_funct_1(X36)))&((r2_hidden(esk10_2(X36,X42),k1_relat_1(X36))|r2_hidden(esk9_2(X36,X42),X42)|X42=k2_relat_1(X36)|(~v1_relat_1(X36)|~v1_funct_1(X36)))&(esk9_2(X36,X42)=k1_funct_1(X36,esk10_2(X36,X42))|r2_hidden(esk9_2(X36,X42),X42)|X42=k2_relat_1(X36)|(~v1_relat_1(X36)|~v1_funct_1(X36)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.63/0.79  fof(c_0_12, negated_conjecture, ~(![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0)), inference(assume_negation,[status(cth)],[t16_funct_1])).
% 0.63/0.79  fof(c_0_13, plain, ![X5, X6]:(~r2_hidden(X5,X6)|~r2_hidden(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.63/0.79  cnf(c_0_14, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.63/0.79  fof(c_0_15, negated_conjecture, ![X57, X58]:((~v1_relat_1(X57)|~v1_funct_1(X57)|(~v1_relat_1(X58)|~v1_funct_1(X58)|(k1_relat_1(X57)!=esk14_0|k1_relat_1(X58)!=esk14_0|X57=X58)))&esk14_0!=k1_xboole_0), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).
% 0.63/0.79  fof(c_0_16, plain, ![X50, X52]:(((v1_relat_1(esk12_1(X50))&v1_funct_1(esk12_1(X50)))&k1_relat_1(esk12_1(X50))=X50)&(~r2_hidden(X52,X50)|k1_funct_1(esk12_1(X50),X52)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).
% 0.63/0.79  fof(c_0_17, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X14,X13)|(X14=X11|X14=X12)|X13!=k2_tarski(X11,X12))&((X15!=X11|r2_hidden(X15,X13)|X13!=k2_tarski(X11,X12))&(X15!=X12|r2_hidden(X15,X13)|X13!=k2_tarski(X11,X12))))&(((esk2_3(X16,X17,X18)!=X16|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_tarski(X16,X17))&(esk2_3(X16,X17,X18)!=X17|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_tarski(X16,X17)))&(r2_hidden(esk2_3(X16,X17,X18),X18)|(esk2_3(X16,X17,X18)=X16|esk2_3(X16,X17,X18)=X17)|X18=k2_tarski(X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.63/0.79  fof(c_0_18, plain, ![X20, X21]:k1_enumset1(X20,X20,X21)=k2_tarski(X20,X21), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.63/0.79  cnf(c_0_19, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.63/0.79  cnf(c_0_20, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_14])])).
% 0.63/0.79  fof(c_0_21, plain, ![X46, X47, X49]:(((v1_relat_1(esk11_2(X46,X47))&v1_funct_1(esk11_2(X46,X47)))&k1_relat_1(esk11_2(X46,X47))=X46)&(~r2_hidden(X49,X46)|k1_funct_1(esk11_2(X46,X47),X49)=X47)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.63/0.79  cnf(c_0_22, negated_conjecture, (X1=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k1_relat_1(X1)!=esk14_0|k1_relat_1(X2)!=esk14_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.63/0.79  cnf(c_0_23, plain, (k1_relat_1(esk12_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.63/0.79  cnf(c_0_24, plain, (v1_funct_1(esk12_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.63/0.79  cnf(c_0_25, plain, (v1_relat_1(esk12_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.63/0.79  fof(c_0_26, plain, ![X22, X23, X24, X26, X27, X28, X29, X31]:(((~r2_hidden(X24,X23)|r2_hidden(k4_tarski(X24,esk3_3(X22,X23,X24)),X22)|X23!=k1_relat_1(X22))&(~r2_hidden(k4_tarski(X26,X27),X22)|r2_hidden(X26,X23)|X23!=k1_relat_1(X22)))&((~r2_hidden(esk4_2(X28,X29),X29)|~r2_hidden(k4_tarski(esk4_2(X28,X29),X31),X28)|X29=k1_relat_1(X28))&(r2_hidden(esk4_2(X28,X29),X29)|r2_hidden(k4_tarski(esk4_2(X28,X29),esk5_2(X28,X29)),X28)|X29=k1_relat_1(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.63/0.79  cnf(c_0_27, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.63/0.79  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.63/0.79  cnf(c_0_29, plain, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k2_relat_1(X1),k1_funct_1(X1,X2))|~r2_hidden(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.63/0.79  cnf(c_0_30, plain, (k1_funct_1(esk11_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.63/0.79  cnf(c_0_31, plain, (v1_funct_1(esk11_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.63/0.79  cnf(c_0_32, plain, (v1_relat_1(esk11_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.63/0.79  cnf(c_0_33, plain, (k1_relat_1(esk11_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.63/0.79  cnf(c_0_34, negated_conjecture, (X1=esk12_1(esk14_0)|k1_relat_1(X1)!=esk14_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])])])).
% 0.63/0.79  cnf(c_0_35, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.63/0.79  cnf(c_0_36, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X4,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.63/0.79  cnf(c_0_37, plain, (~r2_hidden(k2_relat_1(esk11_2(X1,X2)),X2)|~r2_hidden(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32]), c_0_33])])).
% 0.63/0.79  cnf(c_0_38, negated_conjecture, (esk11_2(esk14_0,X1)=esk12_1(esk14_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_33]), c_0_31]), c_0_32])])])).
% 0.63/0.79  cnf(c_0_39, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_35])).
% 0.63/0.79  cnf(c_0_40, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_36])])).
% 0.63/0.79  fof(c_0_41, plain, ![X53, X55]:(((v1_relat_1(esk13_1(X53))&v1_funct_1(esk13_1(X53)))&k1_relat_1(esk13_1(X53))=X53)&(~r2_hidden(X55,X53)|k1_funct_1(esk13_1(X53),X55)=np__1)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e7_25__funct_1])])])])).
% 0.63/0.79  cnf(c_0_42, negated_conjecture, (~r2_hidden(k2_relat_1(esk12_1(esk14_0)),X1)|~r2_hidden(X2,esk14_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.63/0.79  cnf(c_0_43, plain, (r2_hidden(X1,k1_relat_1(k1_enumset1(X2,X2,k4_tarski(X1,X3))))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.63/0.79  cnf(c_0_44, plain, (r2_hidden(esk8_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.63/0.79  cnf(c_0_45, plain, (k1_relat_1(esk13_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.63/0.79  cnf(c_0_46, plain, (v1_funct_1(esk13_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.63/0.79  cnf(c_0_47, plain, (v1_relat_1(esk13_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.63/0.79  cnf(c_0_48, negated_conjecture, (~r2_hidden(X1,esk14_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.63/0.79  cnf(c_0_49, plain, (r2_hidden(esk4_2(X1,X2),X2)|r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)|X2=k1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.63/0.79  fof(c_0_50, plain, ![X33]:(~v1_relat_1(X33)|(r2_hidden(k4_tarski(esk6_1(X33),esk7_1(X33)),X33)|X33=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).
% 0.63/0.79  cnf(c_0_51, plain, (r2_hidden(esk8_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_44])).
% 0.63/0.79  cnf(c_0_52, negated_conjecture, (X1=esk13_1(esk14_0)|k1_relat_1(X1)!=esk14_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_45]), c_0_46]), c_0_47])])])).
% 0.63/0.79  cnf(c_0_53, negated_conjecture, (X1=k1_relat_1(esk14_0)|r2_hidden(esk4_2(esk14_0,X1),X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.63/0.79  cnf(c_0_54, plain, (r2_hidden(k4_tarski(esk6_1(X1),esk7_1(X1)),X1)|X1=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.63/0.79  cnf(c_0_55, plain, (r2_hidden(esk8_3(esk13_1(X1),k2_relat_1(esk13_1(X1)),X2),X1)|~r2_hidden(X2,k2_relat_1(esk13_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_45]), c_0_46]), c_0_47])])).
% 0.63/0.79  cnf(c_0_56, negated_conjecture, (esk13_1(esk14_0)=esk12_1(esk14_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_23]), c_0_24]), c_0_25])])])).
% 0.63/0.79  cnf(c_0_57, negated_conjecture, (k1_relat_1(esk14_0)=esk14_0), inference(spm,[status(thm)],[c_0_48, c_0_53])).
% 0.63/0.79  cnf(c_0_58, plain, (esk13_1(X1)=k1_xboole_0|r2_hidden(k4_tarski(esk6_1(esk13_1(X1)),esk7_1(esk13_1(X1))),esk13_1(X1))), inference(spm,[status(thm)],[c_0_54, c_0_47])).
% 0.63/0.79  cnf(c_0_59, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk12_1(esk14_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_55]), c_0_56])).
% 0.63/0.79  cnf(c_0_60, negated_conjecture, (X1=esk14_0|r2_hidden(esk4_2(esk14_0,X1),X1)), inference(rw,[status(thm)],[c_0_53, c_0_57])).
% 0.63/0.79  cnf(c_0_61, plain, (esk13_1(X1)=k1_xboole_0|r2_hidden(esk6_1(esk13_1(X1)),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_58]), c_0_45])).
% 0.63/0.79  cnf(c_0_62, negated_conjecture, (k2_relat_1(esk12_1(esk14_0))=esk14_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.63/0.79  cnf(c_0_63, negated_conjecture, (esk12_1(esk14_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_61]), c_0_56])).
% 0.63/0.79  cnf(c_0_64, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.63/0.79  cnf(c_0_65, negated_conjecture, (esk14_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.63/0.79  cnf(c_0_66, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_65]), ['proof']).
% 0.63/0.79  # SZS output end CNFRefutation
% 0.63/0.79  # Proof object total steps             : 67
% 0.63/0.79  # Proof object clause steps            : 45
% 0.63/0.79  # Proof object formula steps           : 22
% 0.63/0.79  # Proof object conjectures             : 18
% 0.63/0.79  # Proof object clause conjectures      : 15
% 0.63/0.79  # Proof object formula conjectures     : 3
% 0.63/0.79  # Proof object initial clauses used    : 21
% 0.63/0.79  # Proof object initial formulas used   : 11
% 0.63/0.79  # Proof object generating inferences   : 17
% 0.63/0.79  # Proof object simplifying inferences  : 37
% 0.63/0.79  # Training examples: 0 positive, 0 negative
% 0.63/0.79  # Parsed axioms                        : 12
% 0.63/0.79  # Removed by relevancy pruning/SinE    : 0
% 0.63/0.79  # Initial clauses                      : 37
% 0.63/0.79  # Removed in clause preprocessing      : 1
% 0.63/0.79  # Initial clauses in saturation        : 36
% 0.63/0.79  # Processed clauses                    : 2190
% 0.63/0.79  # ...of these trivial                  : 4
% 0.63/0.79  # ...subsumed                          : 1558
% 0.63/0.79  # ...remaining for further processing  : 628
% 0.63/0.79  # Other redundant clauses eliminated   : 204
% 0.63/0.79  # Clauses deleted for lack of memory   : 0
% 0.63/0.79  # Backward-subsumed                    : 55
% 0.63/0.79  # Backward-rewritten                   : 61
% 0.63/0.79  # Generated clauses                    : 25443
% 0.63/0.79  # ...of the previous two non-trivial   : 22863
% 0.63/0.79  # Contextual simplify-reflections      : 13
% 0.63/0.79  # Paramodulations                      : 25146
% 0.63/0.79  # Factorizations                       : 96
% 0.63/0.79  # Equation resolutions                 : 204
% 0.63/0.79  # Propositional unsat checks           : 0
% 0.63/0.79  #    Propositional check models        : 0
% 0.63/0.79  #    Propositional check unsatisfiable : 0
% 0.63/0.79  #    Propositional clauses             : 0
% 0.63/0.79  #    Propositional clauses after purity: 0
% 0.63/0.79  #    Propositional unsat core size     : 0
% 0.63/0.79  #    Propositional preprocessing time  : 0.000
% 0.63/0.79  #    Propositional encoding time       : 0.000
% 0.63/0.79  #    Propositional solver time         : 0.000
% 0.63/0.79  #    Success case prop preproc time    : 0.000
% 0.63/0.79  #    Success case prop encoding time   : 0.000
% 0.63/0.79  #    Success case prop solver time     : 0.000
% 0.63/0.79  # Current number of processed clauses  : 468
% 0.63/0.79  #    Positive orientable unit clauses  : 20
% 0.63/0.79  #    Positive unorientable unit clauses: 0
% 0.63/0.79  #    Negative unit clauses             : 12
% 0.63/0.79  #    Non-unit-clauses                  : 436
% 0.63/0.79  # Current number of unprocessed clauses: 19888
% 0.63/0.79  # ...number of literals in the above   : 124181
% 0.63/0.79  # Current number of archived formulas  : 0
% 0.63/0.79  # Current number of archived clauses   : 153
% 0.63/0.79  # Clause-clause subsumption calls (NU) : 37099
% 0.63/0.79  # Rec. Clause-clause subsumption calls : 15172
% 0.63/0.79  # Non-unit clause-clause subsumptions  : 586
% 0.63/0.79  # Unit Clause-clause subsumption calls : 698
% 0.63/0.79  # Rewrite failures with RHS unbound    : 0
% 0.63/0.79  # BW rewrite match attempts            : 158
% 0.63/0.79  # BW rewrite match successes           : 10
% 0.63/0.79  # Condensation attempts                : 0
% 0.63/0.79  # Condensation successes               : 0
% 0.63/0.79  # Termbank termtop insertions          : 542260
% 0.63/0.79  
% 0.63/0.79  # -------------------------------------------------
% 0.63/0.79  # User time                : 0.437 s
% 0.63/0.79  # System time              : 0.012 s
% 0.63/0.79  # Total time               : 0.449 s
% 0.63/0.79  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
