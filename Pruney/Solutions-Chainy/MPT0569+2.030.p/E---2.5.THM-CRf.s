%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:37 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 154 expanded)
%              Number of clauses        :   33 (  72 expanded)
%              Number of leaves         :    6 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  140 ( 533 expanded)
%              Number of equality atoms :   19 (  75 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(c_0_6,plain,(
    ! [X14,X15] :
      ( ~ r1_xboole_0(k1_tarski(X14),X15)
      | ~ r2_hidden(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_7,plain,(
    ! [X13] : r1_xboole_0(X13,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_8,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X16,X17,X18,X20,X21,X22,X23,X25] :
      ( ( ~ r2_hidden(X18,X17)
        | r2_hidden(k4_tarski(esk3_3(X16,X17,X18),X18),X16)
        | X17 != k2_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(X21,X20),X16)
        | r2_hidden(X20,X17)
        | X17 != k2_relat_1(X16) )
      & ( ~ r2_hidden(esk4_2(X22,X23),X23)
        | ~ r2_hidden(k4_tarski(X25,esk4_2(X22,X23)),X22)
        | X23 = k2_relat_1(X22) )
      & ( r2_hidden(esk4_2(X22,X23),X23)
        | r2_hidden(k4_tarski(esk5_2(X22,X23),esk4_2(X22,X23)),X22)
        | X23 = k2_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_11,plain,(
    ! [X5,X6,X8,X9,X10] :
      ( ( r2_hidden(esk1_2(X5,X6),X5)
        | r1_xboole_0(X5,X6) )
      & ( r2_hidden(esk1_2(X5,X6),X6)
        | r1_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | ~ r1_xboole_0(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_12,plain,(
    ! [X27,X28,X29,X31] :
      ( ( r2_hidden(esk6_3(X27,X28,X29),k2_relat_1(X29))
        | ~ r2_hidden(X27,k10_relat_1(X29,X28))
        | ~ v1_relat_1(X29) )
      & ( r2_hidden(k4_tarski(X27,esk6_3(X27,X28,X29)),X29)
        | ~ r2_hidden(X27,k10_relat_1(X29,X28))
        | ~ v1_relat_1(X29) )
      & ( r2_hidden(esk6_3(X27,X28,X29),X28)
        | ~ r2_hidden(X27,k10_relat_1(X29,X28))
        | ~ v1_relat_1(X29) )
      & ( ~ r2_hidden(X31,k2_relat_1(X29))
        | ~ r2_hidden(k4_tarski(X27,X31),X29)
        | ~ r2_hidden(X31,X28)
        | r2_hidden(X27,k10_relat_1(X29,X28))
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk5_2(X1,X2),esk4_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( X1 = k2_relat_1(k1_xboole_0)
    | r2_hidden(esk4_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(esk6_3(X2,X3,X1),X4)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ r1_xboole_0(X4,X3) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_17])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

cnf(c_0_23,plain,
    ( r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(esk3_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ r1_xboole_0(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[c_0_17,c_0_21])).

fof(c_0_28,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & ( k10_relat_1(esk8_0,esk7_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk8_0),esk7_0) )
    & ( k10_relat_1(esk8_0,esk7_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk8_0),esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( k10_relat_1(esk8_0,esk7_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk8_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( k10_relat_1(esk8_0,esk7_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk8_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_33])]),c_0_13])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(X1,k2_relat_1(esk8_0))
    | ~ r2_hidden(esk1_2(X1,k2_relat_1(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( k10_relat_1(esk8_0,esk7_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk8_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( r1_xboole_0(esk7_0,k2_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(esk8_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_35])])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:28:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.47/0.69  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.47/0.69  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.47/0.69  #
% 0.47/0.69  # Preprocessing time       : 0.022 s
% 0.47/0.69  
% 0.47/0.69  # Proof found!
% 0.47/0.69  # SZS status Theorem
% 0.47/0.69  # SZS output start CNFRefutation
% 0.47/0.69  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.47/0.69  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.47/0.69  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.47/0.69  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.47/0.69  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.47/0.69  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 0.47/0.69  fof(c_0_6, plain, ![X14, X15]:(~r1_xboole_0(k1_tarski(X14),X15)|~r2_hidden(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.47/0.69  fof(c_0_7, plain, ![X13]:r1_xboole_0(X13,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.47/0.69  cnf(c_0_8, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.47/0.69  cnf(c_0_9, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.47/0.69  fof(c_0_10, plain, ![X16, X17, X18, X20, X21, X22, X23, X25]:(((~r2_hidden(X18,X17)|r2_hidden(k4_tarski(esk3_3(X16,X17,X18),X18),X16)|X17!=k2_relat_1(X16))&(~r2_hidden(k4_tarski(X21,X20),X16)|r2_hidden(X20,X17)|X17!=k2_relat_1(X16)))&((~r2_hidden(esk4_2(X22,X23),X23)|~r2_hidden(k4_tarski(X25,esk4_2(X22,X23)),X22)|X23=k2_relat_1(X22))&(r2_hidden(esk4_2(X22,X23),X23)|r2_hidden(k4_tarski(esk5_2(X22,X23),esk4_2(X22,X23)),X22)|X23=k2_relat_1(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.47/0.69  fof(c_0_11, plain, ![X5, X6, X8, X9, X10]:(((r2_hidden(esk1_2(X5,X6),X5)|r1_xboole_0(X5,X6))&(r2_hidden(esk1_2(X5,X6),X6)|r1_xboole_0(X5,X6)))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|~r1_xboole_0(X8,X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.47/0.69  fof(c_0_12, plain, ![X27, X28, X29, X31]:((((r2_hidden(esk6_3(X27,X28,X29),k2_relat_1(X29))|~r2_hidden(X27,k10_relat_1(X29,X28))|~v1_relat_1(X29))&(r2_hidden(k4_tarski(X27,esk6_3(X27,X28,X29)),X29)|~r2_hidden(X27,k10_relat_1(X29,X28))|~v1_relat_1(X29)))&(r2_hidden(esk6_3(X27,X28,X29),X28)|~r2_hidden(X27,k10_relat_1(X29,X28))|~v1_relat_1(X29)))&(~r2_hidden(X31,k2_relat_1(X29))|~r2_hidden(k4_tarski(X27,X31),X29)|~r2_hidden(X31,X28)|r2_hidden(X27,k10_relat_1(X29,X28))|~v1_relat_1(X29))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.47/0.69  cnf(c_0_13, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.47/0.69  cnf(c_0_14, plain, (r2_hidden(esk4_2(X1,X2),X2)|r2_hidden(k4_tarski(esk5_2(X1,X2),esk4_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.69  cnf(c_0_15, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.47/0.69  cnf(c_0_16, plain, (r2_hidden(esk6_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.69  cnf(c_0_17, plain, (X1=k2_relat_1(k1_xboole_0)|r2_hidden(esk4_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.47/0.69  cnf(c_0_18, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.69  cnf(c_0_19, plain, (~v1_relat_1(X1)|~r2_hidden(esk6_3(X2,X3,X1),X4)|~r2_hidden(X2,k10_relat_1(X1,X3))|~r1_xboole_0(X4,X3)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.47/0.69  cnf(c_0_20, plain, (r2_hidden(esk6_3(X1,X2,X3),k2_relat_1(X3))|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.69  cnf(c_0_21, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_13, c_0_17])).
% 0.47/0.69  fof(c_0_22, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.47/0.69  cnf(c_0_23, plain, (r2_hidden(X3,k10_relat_1(X2,X4))|~r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.69  cnf(c_0_24, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_18])).
% 0.47/0.69  cnf(c_0_25, plain, (r2_hidden(k4_tarski(esk3_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.69  cnf(c_0_26, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,X3))|~r1_xboole_0(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.47/0.69  cnf(c_0_27, plain, (X1=k1_xboole_0|r2_hidden(esk4_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[c_0_17, c_0_21])).
% 0.47/0.69  fof(c_0_28, negated_conjecture, (v1_relat_1(esk8_0)&((k10_relat_1(esk8_0,esk7_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk8_0),esk7_0))&(k10_relat_1(esk8_0,esk7_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk8_0),esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.47/0.69  cnf(c_0_29, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_23, c_0_24])).
% 0.47/0.69  cnf(c_0_30, plain, (r2_hidden(k4_tarski(esk3_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_25])).
% 0.47/0.69  cnf(c_0_31, plain, (k10_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.47/0.69  cnf(c_0_32, negated_conjecture, (k10_relat_1(esk8_0,esk7_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk8_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.47/0.69  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.47/0.69  cnf(c_0_34, plain, (r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.47/0.69  cnf(c_0_35, negated_conjecture, (k10_relat_1(esk8_0,esk7_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.47/0.69  cnf(c_0_36, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.47/0.69  cnf(c_0_37, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk8_0))|~r2_hidden(X1,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_33])]), c_0_13])).
% 0.47/0.69  cnf(c_0_38, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.47/0.69  cnf(c_0_39, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_15, c_0_36])).
% 0.47/0.69  cnf(c_0_40, negated_conjecture, (r1_xboole_0(X1,k2_relat_1(esk8_0))|~r2_hidden(esk1_2(X1,k2_relat_1(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.47/0.69  cnf(c_0_41, negated_conjecture, (k10_relat_1(esk8_0,esk7_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk8_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.47/0.69  cnf(c_0_42, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 0.47/0.69  cnf(c_0_43, negated_conjecture, (r1_xboole_0(esk7_0,k2_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_40, c_0_36])).
% 0.47/0.69  cnf(c_0_44, negated_conjecture, (~r1_xboole_0(k2_relat_1(esk8_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_35])])).
% 0.47/0.69  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), ['proof']).
% 0.47/0.69  # SZS output end CNFRefutation
% 0.47/0.69  # Proof object total steps             : 46
% 0.47/0.69  # Proof object clause steps            : 33
% 0.47/0.69  # Proof object formula steps           : 13
% 0.47/0.69  # Proof object conjectures             : 12
% 0.47/0.69  # Proof object clause conjectures      : 9
% 0.47/0.69  # Proof object formula conjectures     : 3
% 0.47/0.69  # Proof object initial clauses used    : 14
% 0.47/0.69  # Proof object initial formulas used   : 6
% 0.47/0.69  # Proof object generating inferences   : 14
% 0.47/0.69  # Proof object simplifying inferences  : 12
% 0.47/0.69  # Training examples: 0 positive, 0 negative
% 0.47/0.69  # Parsed axioms                        : 7
% 0.47/0.69  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.69  # Initial clauses                      : 17
% 0.47/0.69  # Removed in clause preprocessing      : 0
% 0.47/0.69  # Initial clauses in saturation        : 17
% 0.47/0.69  # Processed clauses                    : 5271
% 0.47/0.69  # ...of these trivial                  : 0
% 0.47/0.69  # ...subsumed                          : 4876
% 0.47/0.69  # ...remaining for further processing  : 395
% 0.47/0.69  # Other redundant clauses eliminated   : 2
% 0.47/0.69  # Clauses deleted for lack of memory   : 0
% 0.47/0.69  # Backward-subsumed                    : 8
% 0.47/0.69  # Backward-rewritten                   : 4
% 0.47/0.69  # Generated clauses                    : 26849
% 0.47/0.69  # ...of the previous two non-trivial   : 25848
% 0.47/0.69  # Contextual simplify-reflections      : 3
% 0.47/0.69  # Paramodulations                      : 26845
% 0.47/0.69  # Factorizations                       : 2
% 0.47/0.69  # Equation resolutions                 : 2
% 0.47/0.69  # Propositional unsat checks           : 0
% 0.47/0.69  #    Propositional check models        : 0
% 0.47/0.69  #    Propositional check unsatisfiable : 0
% 0.47/0.69  #    Propositional clauses             : 0
% 0.47/0.69  #    Propositional clauses after purity: 0
% 0.47/0.69  #    Propositional unsat core size     : 0
% 0.47/0.69  #    Propositional preprocessing time  : 0.000
% 0.47/0.69  #    Propositional encoding time       : 0.000
% 0.47/0.69  #    Propositional solver time         : 0.000
% 0.47/0.69  #    Success case prop preproc time    : 0.000
% 0.47/0.69  #    Success case prop encoding time   : 0.000
% 0.47/0.69  #    Success case prop solver time     : 0.000
% 0.47/0.69  # Current number of processed clauses  : 381
% 0.47/0.69  #    Positive orientable unit clauses  : 7
% 0.47/0.69  #    Positive unorientable unit clauses: 0
% 0.47/0.69  #    Negative unit clauses             : 2
% 0.47/0.69  #    Non-unit-clauses                  : 372
% 0.47/0.69  # Current number of unprocessed clauses: 20491
% 0.47/0.69  # ...number of literals in the above   : 93595
% 0.47/0.69  # Current number of archived formulas  : 0
% 0.47/0.69  # Current number of archived clauses   : 12
% 0.47/0.69  # Clause-clause subsumption calls (NU) : 101537
% 0.47/0.69  # Rec. Clause-clause subsumption calls : 83789
% 0.47/0.69  # Non-unit clause-clause subsumptions  : 4407
% 0.47/0.69  # Unit Clause-clause subsumption calls : 2
% 0.47/0.69  # Rewrite failures with RHS unbound    : 0
% 0.47/0.69  # BW rewrite match attempts            : 2
% 0.47/0.69  # BW rewrite match successes           : 2
% 0.47/0.69  # Condensation attempts                : 0
% 0.47/0.69  # Condensation successes               : 0
% 0.47/0.69  # Termbank termtop insertions          : 435922
% 0.47/0.69  
% 0.47/0.69  # -------------------------------------------------
% 0.47/0.69  # User time                : 0.344 s
% 0.47/0.69  # System time              : 0.012 s
% 0.47/0.69  # Total time               : 0.356 s
% 0.47/0.69  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
