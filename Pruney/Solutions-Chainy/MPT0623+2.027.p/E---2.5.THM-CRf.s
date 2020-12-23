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
% DateTime   : Thu Dec  3 10:53:09 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 135 expanded)
%              Number of clauses        :   43 (  60 expanded)
%              Number of leaves         :   11 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :  198 ( 517 expanded)
%              Number of equality atoms :   84 ( 229 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t18_funct_1,conjecture,(
    ! [X1,X2] :
      ~ ( ~ ( X1 = k1_xboole_0
            & X2 != k1_xboole_0 )
        & ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ~ ( X2 = k1_relat_1(X3)
                & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t15_funct_1,axiom,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => ! [X2] :
        ? [X3] :
          ( v1_relat_1(X3)
          & v1_funct_1(X3)
          & k1_relat_1(X3) = X1
          & k2_relat_1(X3) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(s3_funct_1__e2_25__funct_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_11,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_xboole_0(X11,X12) )
      & ( r2_hidden(esk2_2(X11,X12),X12)
        | r1_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_12,plain,(
    ! [X18] : r1_xboole_0(X18,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_13,plain,(
    ! [X26,X27,X28,X30,X31,X32,X33,X35] :
      ( ( ~ r2_hidden(X28,X27)
        | r2_hidden(k4_tarski(X28,esk4_3(X26,X27,X28)),X26)
        | X27 != k1_relat_1(X26) )
      & ( ~ r2_hidden(k4_tarski(X30,X31),X26)
        | r2_hidden(X30,X27)
        | X27 != k1_relat_1(X26) )
      & ( ~ r2_hidden(esk5_2(X32,X33),X33)
        | ~ r2_hidden(k4_tarski(esk5_2(X32,X33),X35),X32)
        | X33 = k1_relat_1(X32) )
      & ( r2_hidden(esk5_2(X32,X33),X33)
        | r2_hidden(k4_tarski(esk5_2(X32,X33),esk6_2(X32,X33)),X32)
        | X33 = k1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_14,plain,(
    ! [X19,X20,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X21,X20)
        | X21 = X19
        | X20 != k1_tarski(X19) )
      & ( X22 != X19
        | r2_hidden(X22,X20)
        | X20 != k1_tarski(X19) )
      & ( ~ r2_hidden(esk3_2(X23,X24),X24)
        | esk3_2(X23,X24) != X23
        | X24 = k1_tarski(X23) )
      & ( r2_hidden(esk3_2(X23,X24),X24)
        | esk3_2(X23,X24) = X23
        | X24 = k1_tarski(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( ~ ( X1 = k1_xboole_0
              & X2 != k1_xboole_0 )
          & ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ~ ( X2 = k1_relat_1(X3)
                  & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_funct_1])).

cnf(c_0_20,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | esk3_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).

fof(c_0_26,negated_conjecture,(
    ! [X52] :
      ( ( esk10_0 != k1_xboole_0
        | esk11_0 = k1_xboole_0 )
      & ( ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52)
        | esk11_0 != k1_relat_1(X52)
        | ~ r1_tarski(k2_relat_1(X52),esk10_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])])).

fof(c_0_27,plain,(
    ! [X47,X48] :
      ( ( v1_relat_1(esk9_2(X47,X48))
        | X47 = k1_xboole_0 )
      & ( v1_funct_1(esk9_2(X47,X48))
        | X47 = k1_xboole_0 )
      & ( k1_relat_1(esk9_2(X47,X48)) = X47
        | X47 = k1_xboole_0 )
      & ( k2_relat_1(esk9_2(X47,X48)) = k1_tarski(X48)
        | X47 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_funct_1])])])])])).

cnf(c_0_28,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X37] :
      ( ( k1_relat_1(X37) != k1_xboole_0
        | k2_relat_1(X37) = k1_xboole_0
        | ~ v1_relat_1(X37) )
      & ( k2_relat_1(X37) != k1_xboole_0
        | k1_relat_1(X37) = k1_xboole_0
        | ~ v1_relat_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

fof(c_0_31,plain,(
    ! [X17] : r1_tarski(k1_xboole_0,X17) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_32,plain,
    ( esk3_2(X1,k1_xboole_0) = X1
    | k1_tarski(X1) = k1_xboole_0
    | ~ r2_hidden(esk3_2(X1,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k1_relat_1(k1_tarski(k4_tarski(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | esk11_0 != k1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k2_relat_1(esk9_2(X1,X2)) = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( v1_relat_1(esk9_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( v1_funct_1(esk9_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,plain,
    ( esk1_2(k1_tarski(X1),X2) = X1
    | r1_tarski(k1_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_40,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_42,plain,(
    ! [X42,X44] :
      ( v1_relat_1(esk8_1(X42))
      & v1_funct_1(esk8_1(X42))
      & k1_relat_1(esk8_1(X42)) = X42
      & ( ~ r2_hidden(X44,X42)
        | k1_funct_1(esk8_1(X42),X44) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).

cnf(c_0_43,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_44,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | esk3_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_45,plain,
    ( esk3_2(X1,k1_xboole_0) = X1
    | k1_tarski(X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( X1 = k1_xboole_0
    | k1_relat_1(esk9_2(X1,X2)) != esk11_0
    | ~ r1_tarski(k1_tarski(X2),esk10_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( k1_relat_1(X1) != esk11_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_40]),c_0_41])])).

cnf(c_0_49,plain,
    ( v1_funct_1(esk8_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( k1_relat_1(esk8_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( v1_relat_1(esk8_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_25])).

cnf(c_0_53,plain,
    ( k1_tarski(X1) = k1_xboole_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( X1 = k1_xboole_0
    | k1_relat_1(esk9_2(X1,X2)) != esk11_0
    | ~ r2_hidden(X2,esk10_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,plain,
    ( k1_relat_1(esk9_2(X1,X2)) = X1
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_56,negated_conjecture,
    ( esk11_0 != k1_xboole_0 ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_50]),c_0_51])])])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_41])]),c_0_22])).

cnf(c_0_58,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_59,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(X1,esk10_0) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55])]),c_0_56])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk5_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | esk10_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_63,negated_conjecture,
    ( esk10_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:42:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.21/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.028 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.21/0.39  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.21/0.39  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.21/0.39  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.21/0.39  fof(t18_funct_1, conjecture, ![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 0.21/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.39  fof(t15_funct_1, axiom, ![X1]:(X1!=k1_xboole_0=>![X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&k2_relat_1(X3)=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 0.21/0.39  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 0.21/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.39  fof(s3_funct_1__e2_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 0.21/0.39  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.21/0.39  fof(c_0_11, plain, ![X11, X12, X14, X15, X16]:(((r2_hidden(esk2_2(X11,X12),X11)|r1_xboole_0(X11,X12))&(r2_hidden(esk2_2(X11,X12),X12)|r1_xboole_0(X11,X12)))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|~r1_xboole_0(X14,X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.21/0.39  fof(c_0_12, plain, ![X18]:r1_xboole_0(X18,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.21/0.39  fof(c_0_13, plain, ![X26, X27, X28, X30, X31, X32, X33, X35]:(((~r2_hidden(X28,X27)|r2_hidden(k4_tarski(X28,esk4_3(X26,X27,X28)),X26)|X27!=k1_relat_1(X26))&(~r2_hidden(k4_tarski(X30,X31),X26)|r2_hidden(X30,X27)|X27!=k1_relat_1(X26)))&((~r2_hidden(esk5_2(X32,X33),X33)|~r2_hidden(k4_tarski(esk5_2(X32,X33),X35),X32)|X33=k1_relat_1(X32))&(r2_hidden(esk5_2(X32,X33),X33)|r2_hidden(k4_tarski(esk5_2(X32,X33),esk6_2(X32,X33)),X32)|X33=k1_relat_1(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.21/0.39  fof(c_0_14, plain, ![X19, X20, X21, X22, X23, X24]:(((~r2_hidden(X21,X20)|X21=X19|X20!=k1_tarski(X19))&(X22!=X19|r2_hidden(X22,X20)|X20!=k1_tarski(X19)))&((~r2_hidden(esk3_2(X23,X24),X24)|esk3_2(X23,X24)!=X23|X24=k1_tarski(X23))&(r2_hidden(esk3_2(X23,X24),X24)|esk3_2(X23,X24)=X23|X24=k1_tarski(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.21/0.39  cnf(c_0_15, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_16, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_17, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.39  cnf(c_0_18, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  fof(c_0_19, negated_conjecture, ~(![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1))))))), inference(assume_negation,[status(cth)],[t18_funct_1])).
% 0.21/0.39  cnf(c_0_20, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  fof(c_0_21, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.39  cnf(c_0_22, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.39  cnf(c_0_23, plain, (r2_hidden(esk3_2(X1,X2),X2)|esk3_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_24, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_17])).
% 0.21/0.39  cnf(c_0_25, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).
% 0.21/0.39  fof(c_0_26, negated_conjecture, ![X52]:((esk10_0!=k1_xboole_0|esk11_0=k1_xboole_0)&(~v1_relat_1(X52)|~v1_funct_1(X52)|(esk11_0!=k1_relat_1(X52)|~r1_tarski(k2_relat_1(X52),esk10_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])])).
% 0.21/0.39  fof(c_0_27, plain, ![X47, X48]:((((v1_relat_1(esk9_2(X47,X48))|X47=k1_xboole_0)&(v1_funct_1(esk9_2(X47,X48))|X47=k1_xboole_0))&(k1_relat_1(esk9_2(X47,X48))=X47|X47=k1_xboole_0))&(k2_relat_1(esk9_2(X47,X48))=k1_tarski(X48)|X47=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_funct_1])])])])])).
% 0.21/0.39  cnf(c_0_28, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(er,[status(thm)],[c_0_20])).
% 0.21/0.39  cnf(c_0_29, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.39  fof(c_0_30, plain, ![X37]:((k1_relat_1(X37)!=k1_xboole_0|k2_relat_1(X37)=k1_xboole_0|~v1_relat_1(X37))&(k2_relat_1(X37)!=k1_xboole_0|k1_relat_1(X37)=k1_xboole_0|~v1_relat_1(X37))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.21/0.39  fof(c_0_31, plain, ![X17]:r1_tarski(k1_xboole_0,X17), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.39  cnf(c_0_32, plain, (esk3_2(X1,k1_xboole_0)=X1|k1_tarski(X1)=k1_xboole_0|~r2_hidden(esk3_2(X1,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.21/0.39  cnf(c_0_33, plain, (r2_hidden(X1,k1_relat_1(k1_tarski(k4_tarski(X1,X2))))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.39  cnf(c_0_34, negated_conjecture, (~v1_relat_1(X1)|~v1_funct_1(X1)|esk11_0!=k1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk10_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.39  cnf(c_0_35, plain, (k2_relat_1(esk9_2(X1,X2))=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.39  cnf(c_0_36, plain, (v1_relat_1(esk9_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.39  cnf(c_0_37, plain, (v1_funct_1(esk9_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.39  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.39  cnf(c_0_39, plain, (esk1_2(k1_tarski(X1),X2)=X1|r1_tarski(k1_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.39  cnf(c_0_40, plain, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.39  cnf(c_0_41, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.39  fof(c_0_42, plain, ![X42, X44]:(((v1_relat_1(esk8_1(X42))&v1_funct_1(esk8_1(X42)))&k1_relat_1(esk8_1(X42))=X42)&(~r2_hidden(X44,X42)|k1_funct_1(esk8_1(X42),X44)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).
% 0.21/0.39  cnf(c_0_43, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.39  cnf(c_0_44, plain, (X2=k1_tarski(X1)|~r2_hidden(esk3_2(X1,X2),X2)|esk3_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_45, plain, (esk3_2(X1,k1_xboole_0)=X1|k1_tarski(X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.39  cnf(c_0_46, negated_conjecture, (X1=k1_xboole_0|k1_relat_1(esk9_2(X1,X2))!=esk11_0|~r1_tarski(k1_tarski(X2),esk10_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37])).
% 0.21/0.39  cnf(c_0_47, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.39  cnf(c_0_48, negated_conjecture, (k1_relat_1(X1)!=esk11_0|k1_relat_1(X1)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_40]), c_0_41])])).
% 0.21/0.39  cnf(c_0_49, plain, (v1_funct_1(esk8_1(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.39  cnf(c_0_50, plain, (k1_relat_1(esk8_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.39  cnf(c_0_51, plain, (v1_relat_1(esk8_1(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.39  cnf(c_0_52, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_43, c_0_25])).
% 0.21/0.39  cnf(c_0_53, plain, (k1_tarski(X1)=k1_xboole_0|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.21/0.39  cnf(c_0_54, negated_conjecture, (X1=k1_xboole_0|k1_relat_1(esk9_2(X1,X2))!=esk11_0|~r2_hidden(X2,esk10_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.21/0.39  cnf(c_0_55, plain, (k1_relat_1(esk9_2(X1,X2))=X1|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.39  cnf(c_0_56, negated_conjecture, (esk11_0!=k1_xboole_0), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_50]), c_0_51])])])).
% 0.21/0.39  cnf(c_0_57, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_41])]), c_0_22])).
% 0.21/0.39  cnf(c_0_58, plain, (r2_hidden(esk5_2(X1,X2),X2)|r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X1)|X2=k1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.39  cnf(c_0_59, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.21/0.39  cnf(c_0_60, negated_conjecture, (~r2_hidden(X1,esk10_0)), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55])]), c_0_56])).
% 0.21/0.39  cnf(c_0_61, plain, (X1=k1_xboole_0|r2_hidden(esk5_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])).
% 0.21/0.39  cnf(c_0_62, negated_conjecture, (esk11_0=k1_xboole_0|esk10_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.39  cnf(c_0_63, negated_conjecture, (esk10_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.21/0.39  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63])]), c_0_56]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 65
% 0.21/0.39  # Proof object clause steps            : 43
% 0.21/0.39  # Proof object formula steps           : 22
% 0.21/0.39  # Proof object conjectures             : 12
% 0.21/0.39  # Proof object clause conjectures      : 9
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 23
% 0.21/0.39  # Proof object initial formulas used   : 11
% 0.21/0.39  # Proof object generating inferences   : 16
% 0.21/0.39  # Proof object simplifying inferences  : 22
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 13
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 35
% 0.21/0.39  # Removed in clause preprocessing      : 0
% 0.21/0.39  # Initial clauses in saturation        : 35
% 0.21/0.39  # Processed clauses                    : 177
% 0.21/0.39  # ...of these trivial                  : 0
% 0.21/0.39  # ...subsumed                          : 42
% 0.21/0.39  # ...remaining for further processing  : 135
% 0.21/0.39  # Other redundant clauses eliminated   : 13
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 6
% 0.21/0.39  # Backward-rewritten                   : 22
% 0.21/0.39  # Generated clauses                    : 233
% 0.21/0.39  # ...of the previous two non-trivial   : 208
% 0.21/0.39  # Contextual simplify-reflections      : 7
% 0.21/0.39  # Paramodulations                      : 218
% 0.21/0.39  # Factorizations                       : 3
% 0.21/0.39  # Equation resolutions                 : 13
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
% 0.21/0.39  # Current number of processed clauses  : 68
% 0.21/0.39  #    Positive orientable unit clauses  : 18
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 2
% 0.21/0.39  #    Non-unit-clauses                  : 48
% 0.21/0.39  # Current number of unprocessed clauses: 82
% 0.21/0.39  # ...number of literals in the above   : 262
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 63
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 230
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 126
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 30
% 0.21/0.39  # Unit Clause-clause subsumption calls : 42
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 7
% 0.21/0.39  # BW rewrite match successes           : 3
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 4707
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.037 s
% 0.21/0.39  # System time              : 0.004 s
% 0.21/0.39  # Total time               : 0.041 s
% 0.21/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
