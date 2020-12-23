%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:23 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 101 expanded)
%              Number of clauses        :   23 (  50 expanded)
%              Number of leaves         :    6 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 330 expanded)
%              Number of equality atoms :   55 ( 152 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(t172_relat_1,conjecture,(
    ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

fof(c_0_6,plain,(
    ! [X22,X23] :
      ( ( k4_xboole_0(X22,k1_tarski(X23)) != X22
        | ~ r2_hidden(X23,X22) )
      & ( r2_hidden(X23,X22)
        | k4_xboole_0(X22,k1_tarski(X23)) = X22 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_7,plain,(
    ! [X50,X51,X52,X54,X55,X56,X57,X59] :
      ( ( ~ r2_hidden(X52,X51)
        | r2_hidden(k4_tarski(X52,esk13_3(X50,X51,X52)),X50)
        | X51 != k1_relat_1(X50) )
      & ( ~ r2_hidden(k4_tarski(X54,X55),X50)
        | r2_hidden(X54,X51)
        | X51 != k1_relat_1(X50) )
      & ( ~ r2_hidden(esk14_2(X56,X57),X57)
        | ~ r2_hidden(k4_tarski(esk14_2(X56,X57),X59),X56)
        | X57 = k1_relat_1(X56) )
      & ( r2_hidden(esk14_2(X56,X57),X57)
        | r2_hidden(k4_tarski(esk14_2(X56,X57),esk15_2(X56,X57)),X56)
        | X57 = k1_relat_1(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_8,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( r2_hidden(k4_tarski(X1,esk13_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X9] : k4_xboole_0(k1_xboole_0,X9) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k1_tarski(k4_tarski(X2,esk13_3(X1,X3,X2)))) != X1
    | X3 != k1_relat_1(X1)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X42,X43,X46,X48,X49] :
      ( ( ~ v1_relat_1(X42)
        | ~ r2_hidden(X43,X42)
        | X43 = k4_tarski(esk10_2(X42,X43),esk11_2(X42,X43)) )
      & ( r2_hidden(esk12_1(X46),X46)
        | v1_relat_1(X46) )
      & ( esk12_1(X46) != k4_tarski(X48,X49)
        | v1_relat_1(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

fof(c_0_14,plain,(
    ! [X30,X31,X32,X33,X35,X36,X37,X38,X40] :
      ( ( r2_hidden(k4_tarski(X33,esk7_4(X30,X31,X32,X33)),X30)
        | ~ r2_hidden(X33,X32)
        | X32 != k10_relat_1(X30,X31)
        | ~ v1_relat_1(X30) )
      & ( r2_hidden(esk7_4(X30,X31,X32,X33),X31)
        | ~ r2_hidden(X33,X32)
        | X32 != k10_relat_1(X30,X31)
        | ~ v1_relat_1(X30) )
      & ( ~ r2_hidden(k4_tarski(X35,X36),X30)
        | ~ r2_hidden(X36,X31)
        | r2_hidden(X35,X32)
        | X32 != k10_relat_1(X30,X31)
        | ~ v1_relat_1(X30) )
      & ( ~ r2_hidden(esk8_3(X30,X37,X38),X38)
        | ~ r2_hidden(k4_tarski(esk8_3(X30,X37,X38),X40),X30)
        | ~ r2_hidden(X40,X37)
        | X38 = k10_relat_1(X30,X37)
        | ~ v1_relat_1(X30) )
      & ( r2_hidden(k4_tarski(esk8_3(X30,X37,X38),esk9_3(X30,X37,X38)),X30)
        | r2_hidden(esk8_3(X30,X37,X38),X38)
        | X38 = k10_relat_1(X30,X37)
        | ~ v1_relat_1(X30) )
      & ( r2_hidden(esk9_3(X30,X37,X38),X37)
        | r2_hidden(esk8_3(X30,X37,X38),X38)
        | X38 = k10_relat_1(X30,X37)
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

cnf(c_0_15,plain,
    ( X1 != k1_relat_1(k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(esk12_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(esk14_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk14_2(X1,X2),esk15_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,esk7_4(X2,X3,X4,X1)),X2)
    | ~ r2_hidden(X1,X4)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( v1_relat_1(X1)
    | X1 != k1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( X1 = k1_relat_1(X2)
    | r2_hidden(esk14_2(X2,X1),X1)
    | X2 != k1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_17])).

cnf(c_0_21,plain,
    ( X1 != k1_relat_1(k1_xboole_0)
    | X2 != k10_relat_1(X1,X3)
    | ~ r2_hidden(X4,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_18]),c_0_19])).

cnf(c_0_22,plain,
    ( X1 = k1_relat_1(X2)
    | X1 != k1_relat_1(k1_xboole_0)
    | X2 != k1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_20])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t172_relat_1])).

cnf(c_0_24,plain,
    ( X1 != k1_relat_1(k1_xboole_0)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relat_1(X1)
    | X1 != k1_relat_1(k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( X1 = k1_relat_1(X2)
    | r2_hidden(esk14_2(X2,X1),X1)
    | k4_xboole_0(X2,k1_tarski(k4_tarski(esk14_2(X2,X1),esk15_2(X2,X1)))) != X2 ),
    inference(spm,[status(thm)],[c_0_8,c_0_17])).

fof(c_0_27,negated_conjecture,(
    k10_relat_1(k1_xboole_0,esk16_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_28,plain,
    ( k10_relat_1(X1,X2) = k1_relat_1(X3)
    | X1 != k1_relat_1(k1_xboole_0)
    | X3 != k1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_20])).

cnf(c_0_29,plain,
    ( k1_relat_1(k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( X1 = k1_relat_1(k1_xboole_0)
    | r2_hidden(esk14_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_12])).

cnf(c_0_31,negated_conjecture,
    ( k10_relat_1(k1_xboole_0,esk16_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( k10_relat_1(X1,X2) = k1_relat_1(k1_xboole_0)
    | X1 != k1_relat_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_29])).

cnf(c_0_33,plain,
    ( X1 = k1_relat_1(k1_xboole_0)
    | k4_xboole_0(X1,k1_tarski(esk14_2(k1_xboole_0,X1))) != X1 ),
    inference(spm,[status(thm)],[c_0_8,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_12]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:38:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.51  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.19/0.51  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.51  #
% 0.19/0.51  # Preprocessing time       : 0.029 s
% 0.19/0.51  # Presaturation interreduction done
% 0.19/0.51  
% 0.19/0.51  # Proof found!
% 0.19/0.51  # SZS status Theorem
% 0.19/0.51  # SZS output start CNFRefutation
% 0.19/0.51  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.19/0.51  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.19/0.51  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.19/0.51  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 0.19/0.51  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 0.19/0.51  fof(t172_relat_1, conjecture, ![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 0.19/0.51  fof(c_0_6, plain, ![X22, X23]:((k4_xboole_0(X22,k1_tarski(X23))!=X22|~r2_hidden(X23,X22))&(r2_hidden(X23,X22)|k4_xboole_0(X22,k1_tarski(X23))=X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.19/0.51  fof(c_0_7, plain, ![X50, X51, X52, X54, X55, X56, X57, X59]:(((~r2_hidden(X52,X51)|r2_hidden(k4_tarski(X52,esk13_3(X50,X51,X52)),X50)|X51!=k1_relat_1(X50))&(~r2_hidden(k4_tarski(X54,X55),X50)|r2_hidden(X54,X51)|X51!=k1_relat_1(X50)))&((~r2_hidden(esk14_2(X56,X57),X57)|~r2_hidden(k4_tarski(esk14_2(X56,X57),X59),X56)|X57=k1_relat_1(X56))&(r2_hidden(esk14_2(X56,X57),X57)|r2_hidden(k4_tarski(esk14_2(X56,X57),esk15_2(X56,X57)),X56)|X57=k1_relat_1(X56)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.19/0.51  cnf(c_0_8, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.51  cnf(c_0_9, plain, (r2_hidden(k4_tarski(X1,esk13_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.51  fof(c_0_10, plain, ![X9]:k4_xboole_0(k1_xboole_0,X9)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.19/0.51  cnf(c_0_11, plain, (k4_xboole_0(X1,k1_tarski(k4_tarski(X2,esk13_3(X1,X3,X2))))!=X1|X3!=k1_relat_1(X1)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.19/0.51  cnf(c_0_12, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.51  fof(c_0_13, plain, ![X42, X43, X46, X48, X49]:((~v1_relat_1(X42)|(~r2_hidden(X43,X42)|X43=k4_tarski(esk10_2(X42,X43),esk11_2(X42,X43))))&((r2_hidden(esk12_1(X46),X46)|v1_relat_1(X46))&(esk12_1(X46)!=k4_tarski(X48,X49)|v1_relat_1(X46)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.19/0.51  fof(c_0_14, plain, ![X30, X31, X32, X33, X35, X36, X37, X38, X40]:((((r2_hidden(k4_tarski(X33,esk7_4(X30,X31,X32,X33)),X30)|~r2_hidden(X33,X32)|X32!=k10_relat_1(X30,X31)|~v1_relat_1(X30))&(r2_hidden(esk7_4(X30,X31,X32,X33),X31)|~r2_hidden(X33,X32)|X32!=k10_relat_1(X30,X31)|~v1_relat_1(X30)))&(~r2_hidden(k4_tarski(X35,X36),X30)|~r2_hidden(X36,X31)|r2_hidden(X35,X32)|X32!=k10_relat_1(X30,X31)|~v1_relat_1(X30)))&((~r2_hidden(esk8_3(X30,X37,X38),X38)|(~r2_hidden(k4_tarski(esk8_3(X30,X37,X38),X40),X30)|~r2_hidden(X40,X37))|X38=k10_relat_1(X30,X37)|~v1_relat_1(X30))&((r2_hidden(k4_tarski(esk8_3(X30,X37,X38),esk9_3(X30,X37,X38)),X30)|r2_hidden(esk8_3(X30,X37,X38),X38)|X38=k10_relat_1(X30,X37)|~v1_relat_1(X30))&(r2_hidden(esk9_3(X30,X37,X38),X37)|r2_hidden(esk8_3(X30,X37,X38),X38)|X38=k10_relat_1(X30,X37)|~v1_relat_1(X30))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.19/0.51  cnf(c_0_15, plain, (X1!=k1_relat_1(k1_xboole_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.51  cnf(c_0_16, plain, (r2_hidden(esk12_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.51  cnf(c_0_17, plain, (r2_hidden(esk14_2(X1,X2),X2)|r2_hidden(k4_tarski(esk14_2(X1,X2),esk15_2(X1,X2)),X1)|X2=k1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.51  cnf(c_0_18, plain, (r2_hidden(k4_tarski(X1,esk7_4(X2,X3,X4,X1)),X2)|~r2_hidden(X1,X4)|X4!=k10_relat_1(X2,X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.51  cnf(c_0_19, plain, (v1_relat_1(X1)|X1!=k1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.51  cnf(c_0_20, plain, (X1=k1_relat_1(X2)|r2_hidden(esk14_2(X2,X1),X1)|X2!=k1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_15, c_0_17])).
% 0.19/0.51  cnf(c_0_21, plain, (X1!=k1_relat_1(k1_xboole_0)|X2!=k10_relat_1(X1,X3)|~r2_hidden(X4,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_18]), c_0_19])).
% 0.19/0.51  cnf(c_0_22, plain, (X1=k1_relat_1(X2)|X1!=k1_relat_1(k1_xboole_0)|X2!=k1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_15, c_0_20])).
% 0.19/0.51  fof(c_0_23, negated_conjecture, ~(![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(assume_negation,[status(cth)],[t172_relat_1])).
% 0.19/0.51  cnf(c_0_24, plain, (X1!=k1_relat_1(k1_xboole_0)|~r2_hidden(X2,k10_relat_1(X1,X3))), inference(er,[status(thm)],[c_0_21])).
% 0.19/0.51  cnf(c_0_25, plain, (k1_relat_1(k1_xboole_0)=k1_relat_1(X1)|X1!=k1_relat_1(k1_xboole_0)), inference(er,[status(thm)],[c_0_22])).
% 0.19/0.51  cnf(c_0_26, plain, (X1=k1_relat_1(X2)|r2_hidden(esk14_2(X2,X1),X1)|k4_xboole_0(X2,k1_tarski(k4_tarski(esk14_2(X2,X1),esk15_2(X2,X1))))!=X2), inference(spm,[status(thm)],[c_0_8, c_0_17])).
% 0.19/0.51  fof(c_0_27, negated_conjecture, k10_relat_1(k1_xboole_0,esk16_0)!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.19/0.51  cnf(c_0_28, plain, (k10_relat_1(X1,X2)=k1_relat_1(X3)|X1!=k1_relat_1(k1_xboole_0)|X3!=k1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_20])).
% 0.19/0.51  cnf(c_0_29, plain, (k1_relat_1(k1_relat_1(k1_xboole_0))=k1_relat_1(k1_xboole_0)), inference(er,[status(thm)],[c_0_25])).
% 0.19/0.51  cnf(c_0_30, plain, (X1=k1_relat_1(k1_xboole_0)|r2_hidden(esk14_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_26, c_0_12])).
% 0.19/0.51  cnf(c_0_31, negated_conjecture, (k10_relat_1(k1_xboole_0,esk16_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.51  cnf(c_0_32, plain, (k10_relat_1(X1,X2)=k1_relat_1(k1_xboole_0)|X1!=k1_relat_1(k1_xboole_0)), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_28]), c_0_29])).
% 0.19/0.51  cnf(c_0_33, plain, (X1=k1_relat_1(k1_xboole_0)|k4_xboole_0(X1,k1_tarski(esk14_2(k1_xboole_0,X1)))!=X1), inference(spm,[status(thm)],[c_0_8, c_0_30])).
% 0.19/0.51  cnf(c_0_34, negated_conjecture, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.51  cnf(c_0_35, plain, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_12]), c_0_34]), ['proof']).
% 0.19/0.51  # SZS output end CNFRefutation
% 0.19/0.51  # Proof object total steps             : 36
% 0.19/0.51  # Proof object clause steps            : 23
% 0.19/0.51  # Proof object formula steps           : 13
% 0.19/0.51  # Proof object conjectures             : 5
% 0.19/0.51  # Proof object clause conjectures      : 2
% 0.19/0.51  # Proof object formula conjectures     : 3
% 0.19/0.51  # Proof object initial clauses used    : 7
% 0.19/0.51  # Proof object initial formulas used   : 6
% 0.19/0.51  # Proof object generating inferences   : 16
% 0.19/0.51  # Proof object simplifying inferences  : 3
% 0.19/0.51  # Training examples: 0 positive, 0 negative
% 0.19/0.51  # Parsed axioms                        : 12
% 0.19/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.51  # Initial clauses                      : 35
% 0.19/0.51  # Removed in clause preprocessing      : 0
% 0.19/0.51  # Initial clauses in saturation        : 35
% 0.19/0.51  # Processed clauses                    : 1624
% 0.19/0.51  # ...of these trivial                  : 11
% 0.19/0.51  # ...subsumed                          : 1144
% 0.19/0.51  # ...remaining for further processing  : 469
% 0.19/0.51  # Other redundant clauses eliminated   : 0
% 0.19/0.51  # Clauses deleted for lack of memory   : 0
% 0.19/0.51  # Backward-subsumed                    : 1
% 0.19/0.51  # Backward-rewritten                   : 94
% 0.19/0.51  # Generated clauses                    : 9446
% 0.19/0.51  # ...of the previous two non-trivial   : 8027
% 0.19/0.51  # Contextual simplify-reflections      : 24
% 0.19/0.51  # Paramodulations                      : 9313
% 0.19/0.51  # Factorizations                       : 2
% 0.19/0.51  # Equation resolutions                 : 131
% 0.19/0.51  # Propositional unsat checks           : 0
% 0.19/0.51  #    Propositional check models        : 0
% 0.19/0.51  #    Propositional check unsatisfiable : 0
% 0.19/0.51  #    Propositional clauses             : 0
% 0.19/0.51  #    Propositional clauses after purity: 0
% 0.19/0.51  #    Propositional unsat core size     : 0
% 0.19/0.51  #    Propositional preprocessing time  : 0.000
% 0.19/0.51  #    Propositional encoding time       : 0.000
% 0.19/0.51  #    Propositional solver time         : 0.000
% 0.19/0.51  #    Success case prop preproc time    : 0.000
% 0.19/0.51  #    Success case prop encoding time   : 0.000
% 0.19/0.51  #    Success case prop solver time     : 0.000
% 0.19/0.51  # Current number of processed clauses  : 339
% 0.19/0.51  #    Positive orientable unit clauses  : 10
% 0.19/0.51  #    Positive unorientable unit clauses: 0
% 0.19/0.51  #    Negative unit clauses             : 2
% 0.19/0.51  #    Non-unit-clauses                  : 327
% 0.19/0.51  # Current number of unprocessed clauses: 6249
% 0.19/0.51  # ...number of literals in the above   : 26738
% 0.19/0.51  # Current number of archived formulas  : 0
% 0.19/0.51  # Current number of archived clauses   : 130
% 0.19/0.51  # Clause-clause subsumption calls (NU) : 71392
% 0.19/0.51  # Rec. Clause-clause subsumption calls : 16587
% 0.19/0.51  # Non-unit clause-clause subsumptions  : 646
% 0.19/0.51  # Unit Clause-clause subsumption calls : 908
% 0.19/0.51  # Rewrite failures with RHS unbound    : 0
% 0.19/0.51  # BW rewrite match attempts            : 111
% 0.19/0.51  # BW rewrite match successes           : 12
% 0.19/0.51  # Condensation attempts                : 0
% 0.19/0.51  # Condensation successes               : 0
% 0.19/0.51  # Termbank termtop insertions          : 131335
% 0.19/0.51  
% 0.19/0.51  # -------------------------------------------------
% 0.19/0.51  # User time                : 0.173 s
% 0.19/0.51  # System time              : 0.006 s
% 0.19/0.51  # Total time               : 0.179 s
% 0.19/0.51  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
