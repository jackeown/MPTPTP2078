%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:26 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   39 (  69 expanded)
%              Number of clauses        :   22 (  29 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  125 ( 257 expanded)
%              Number of equality atoms :   26 (  37 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X4),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(t125_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_xboole_0(X1,X2)
          & v2_funct_1(X3) )
       => r1_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t121_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( v2_funct_1(X3)
       => k9_relat_1(X3,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(t56_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),X1)
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(c_0_8,plain,(
    ! [X23,X24] :
      ( ~ r1_xboole_0(k1_tarski(X23),X24)
      | ~ r2_hidden(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_9,plain,(
    ! [X20] : r1_xboole_0(X20,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_10,plain,(
    ! [X25,X26,X27,X28,X30,X31,X32,X33,X35] :
      ( ( r2_hidden(k4_tarski(esk3_4(X25,X26,X27,X28),X28),X25)
        | ~ r2_hidden(X28,X27)
        | X27 != k9_relat_1(X25,X26)
        | ~ v1_relat_1(X25) )
      & ( r2_hidden(esk3_4(X25,X26,X27,X28),X26)
        | ~ r2_hidden(X28,X27)
        | X27 != k9_relat_1(X25,X26)
        | ~ v1_relat_1(X25) )
      & ( ~ r2_hidden(k4_tarski(X31,X30),X25)
        | ~ r2_hidden(X31,X26)
        | r2_hidden(X30,X27)
        | X27 != k9_relat_1(X25,X26)
        | ~ v1_relat_1(X25) )
      & ( ~ r2_hidden(esk4_3(X25,X32,X33),X33)
        | ~ r2_hidden(k4_tarski(X35,esk4_3(X25,X32,X33)),X25)
        | ~ r2_hidden(X35,X32)
        | X33 = k9_relat_1(X25,X32)
        | ~ v1_relat_1(X25) )
      & ( r2_hidden(k4_tarski(esk5_3(X25,X32,X33),esk4_3(X25,X32,X33)),X25)
        | r2_hidden(esk4_3(X25,X32,X33),X33)
        | X33 = k9_relat_1(X25,X32)
        | ~ v1_relat_1(X25) )
      & ( r2_hidden(esk5_3(X25,X32,X33),X32)
        | r2_hidden(esk4_3(X25,X32,X33),X33)
        | X33 = k9_relat_1(X25,X32)
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r1_xboole_0(X1,X2)
            & v2_funct_1(X3) )
         => r1_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t125_funct_1])).

fof(c_0_12,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_13,plain,(
    ! [X57,X58,X59] :
      ( ~ v1_relat_1(X59)
      | ~ v1_funct_1(X59)
      | ~ v2_funct_1(X59)
      | k9_relat_1(X59,k3_xboole_0(X57,X58)) = k3_xboole_0(k9_relat_1(X59,X57),k9_relat_1(X59,X58)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_1])])).

cnf(c_0_14,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk13_0)
    & v1_funct_1(esk13_0)
    & r1_xboole_0(esk11_0,esk12_0)
    & v2_funct_1(esk13_0)
    & ~ r1_xboole_0(k9_relat_1(esk13_0,esk11_0),k9_relat_1(esk13_0,esk12_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k9_relat_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(esk3_4(X1,X2,k9_relat_1(X1,X2),X3),X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X37,X38,X41,X43,X44] :
      ( ( ~ v1_relat_1(X37)
        | ~ r2_hidden(X38,X37)
        | X38 = k4_tarski(esk6_2(X37,X38),esk7_2(X37,X38)) )
      & ( r2_hidden(esk8_1(X41),X41)
        | v1_relat_1(X41) )
      & ( esk8_1(X41) != k4_tarski(X43,X44)
        | v1_relat_1(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_xboole_0(k9_relat_1(esk13_0,esk11_0),k9_relat_1(esk13_0,esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r1_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | k9_relat_1(X1,k3_xboole_0(X2,X3)) != k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( v2_funct_1(esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_28,plain,(
    ! [X54] :
      ( ~ v1_relat_1(X54)
      | r2_hidden(k4_tarski(esk9_1(X54),esk10_1(X54)),X54)
      | X54 = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).

cnf(c_0_29,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(esk8_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( k9_relat_1(esk13_0,k3_xboole_0(esk11_0,esk12_0)) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,negated_conjecture,
    ( r1_xboole_0(esk11_0,esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(esk9_1(X1),esk10_1(X1)),X1)
    | X1 = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( v1_relat_1(k9_relat_1(X1,k1_xboole_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( k9_relat_1(esk13_0,k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_37,plain,
    ( k9_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_34]),c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:35:40 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.14/0.40  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.14/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.40  #
% 0.14/0.40  # Preprocessing time       : 0.028 s
% 0.14/0.40  
% 0.14/0.40  # Proof found!
% 0.14/0.40  # SZS status Theorem
% 0.14/0.40  # SZS output start CNFRefutation
% 0.14/0.40  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.14/0.40  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.14/0.40  fof(d13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X5,X4),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 0.14/0.40  fof(t125_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_xboole_0(X1,X2)&v2_funct_1(X3))=>r1_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_funct_1)).
% 0.14/0.40  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.14/0.40  fof(t121_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k3_xboole_0(X1,X2))=k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_1)).
% 0.14/0.40  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 0.14/0.40  fof(t56_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(![X2, X3]:~(r2_hidden(k4_tarski(X2,X3),X1))=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 0.14/0.40  fof(c_0_8, plain, ![X23, X24]:(~r1_xboole_0(k1_tarski(X23),X24)|~r2_hidden(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.14/0.40  fof(c_0_9, plain, ![X20]:r1_xboole_0(X20,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.14/0.40  fof(c_0_10, plain, ![X25, X26, X27, X28, X30, X31, X32, X33, X35]:((((r2_hidden(k4_tarski(esk3_4(X25,X26,X27,X28),X28),X25)|~r2_hidden(X28,X27)|X27!=k9_relat_1(X25,X26)|~v1_relat_1(X25))&(r2_hidden(esk3_4(X25,X26,X27,X28),X26)|~r2_hidden(X28,X27)|X27!=k9_relat_1(X25,X26)|~v1_relat_1(X25)))&(~r2_hidden(k4_tarski(X31,X30),X25)|~r2_hidden(X31,X26)|r2_hidden(X30,X27)|X27!=k9_relat_1(X25,X26)|~v1_relat_1(X25)))&((~r2_hidden(esk4_3(X25,X32,X33),X33)|(~r2_hidden(k4_tarski(X35,esk4_3(X25,X32,X33)),X25)|~r2_hidden(X35,X32))|X33=k9_relat_1(X25,X32)|~v1_relat_1(X25))&((r2_hidden(k4_tarski(esk5_3(X25,X32,X33),esk4_3(X25,X32,X33)),X25)|r2_hidden(esk4_3(X25,X32,X33),X33)|X33=k9_relat_1(X25,X32)|~v1_relat_1(X25))&(r2_hidden(esk5_3(X25,X32,X33),X32)|r2_hidden(esk4_3(X25,X32,X33),X33)|X33=k9_relat_1(X25,X32)|~v1_relat_1(X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).
% 0.14/0.40  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_xboole_0(X1,X2)&v2_funct_1(X3))=>r1_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t125_funct_1])).
% 0.14/0.40  fof(c_0_12, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.14/0.40  fof(c_0_13, plain, ![X57, X58, X59]:(~v1_relat_1(X59)|~v1_funct_1(X59)|(~v2_funct_1(X59)|k9_relat_1(X59,k3_xboole_0(X57,X58))=k3_xboole_0(k9_relat_1(X59,X57),k9_relat_1(X59,X58)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_1])])).
% 0.14/0.40  cnf(c_0_14, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.40  cnf(c_0_15, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.40  cnf(c_0_16, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.40  fof(c_0_17, negated_conjecture, ((v1_relat_1(esk13_0)&v1_funct_1(esk13_0))&((r1_xboole_0(esk11_0,esk12_0)&v2_funct_1(esk13_0))&~r1_xboole_0(k9_relat_1(esk13_0,esk11_0),k9_relat_1(esk13_0,esk12_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.14/0.40  cnf(c_0_18, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.40  cnf(c_0_19, plain, (k9_relat_1(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.40  cnf(c_0_20, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.14/0.40  cnf(c_0_21, plain, (r2_hidden(esk3_4(X1,X2,k9_relat_1(X1,X2),X3),X2)|~v1_relat_1(X1)|~r2_hidden(X3,k9_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_16])).
% 0.14/0.40  fof(c_0_22, plain, ![X37, X38, X41, X43, X44]:((~v1_relat_1(X37)|(~r2_hidden(X38,X37)|X38=k4_tarski(esk6_2(X37,X38),esk7_2(X37,X38))))&((r2_hidden(esk8_1(X41),X41)|v1_relat_1(X41))&(esk8_1(X41)!=k4_tarski(X43,X44)|v1_relat_1(X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.14/0.40  cnf(c_0_23, negated_conjecture, (~r1_xboole_0(k9_relat_1(esk13_0,esk11_0),k9_relat_1(esk13_0,esk12_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.40  cnf(c_0_24, plain, (r1_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|k9_relat_1(X1,k3_xboole_0(X2,X3))!=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.40  cnf(c_0_25, negated_conjecture, (v2_funct_1(esk13_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.40  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk13_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.40  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk13_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.40  fof(c_0_28, plain, ![X54]:(~v1_relat_1(X54)|(r2_hidden(k4_tarski(esk9_1(X54),esk10_1(X54)),X54)|X54=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).
% 0.14/0.40  cnf(c_0_29, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.40  cnf(c_0_30, plain, (r2_hidden(esk8_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.40  cnf(c_0_31, negated_conjecture, (k9_relat_1(esk13_0,k3_xboole_0(esk11_0,esk12_0))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27])])).
% 0.14/0.40  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.40  cnf(c_0_33, negated_conjecture, (r1_xboole_0(esk11_0,esk12_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.40  cnf(c_0_34, plain, (r2_hidden(k4_tarski(esk9_1(X1),esk10_1(X1)),X1)|X1=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.40  cnf(c_0_35, plain, (v1_relat_1(k9_relat_1(X1,k1_xboole_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.40  cnf(c_0_36, negated_conjecture, (k9_relat_1(esk13_0,k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.14/0.40  cnf(c_0_37, plain, (k9_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_34]), c_0_35])).
% 0.14/0.40  cnf(c_0_38, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_27])]), ['proof']).
% 0.14/0.40  # SZS output end CNFRefutation
% 0.14/0.40  # Proof object total steps             : 39
% 0.14/0.40  # Proof object clause steps            : 22
% 0.14/0.40  # Proof object formula steps           : 17
% 0.14/0.40  # Proof object conjectures             : 11
% 0.14/0.40  # Proof object clause conjectures      : 8
% 0.14/0.40  # Proof object formula conjectures     : 3
% 0.14/0.40  # Proof object initial clauses used    : 13
% 0.14/0.40  # Proof object initial formulas used   : 8
% 0.14/0.40  # Proof object generating inferences   : 8
% 0.14/0.40  # Proof object simplifying inferences  : 10
% 0.14/0.40  # Training examples: 0 positive, 0 negative
% 0.14/0.40  # Parsed axioms                        : 15
% 0.14/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.40  # Initial clauses                      : 30
% 0.14/0.40  # Removed in clause preprocessing      : 0
% 0.14/0.40  # Initial clauses in saturation        : 30
% 0.14/0.40  # Processed clauses                    : 229
% 0.14/0.40  # ...of these trivial                  : 0
% 0.14/0.40  # ...subsumed                          : 123
% 0.14/0.40  # ...remaining for further processing  : 106
% 0.14/0.40  # Other redundant clauses eliminated   : 4
% 0.14/0.40  # Clauses deleted for lack of memory   : 0
% 0.14/0.40  # Backward-subsumed                    : 3
% 0.14/0.40  # Backward-rewritten                   : 11
% 0.14/0.40  # Generated clauses                    : 582
% 0.14/0.40  # ...of the previous two non-trivial   : 445
% 0.14/0.40  # Contextual simplify-reflections      : 8
% 0.14/0.40  # Paramodulations                      : 578
% 0.14/0.40  # Factorizations                       : 0
% 0.14/0.40  # Equation resolutions                 : 4
% 0.14/0.40  # Propositional unsat checks           : 0
% 0.14/0.40  #    Propositional check models        : 0
% 0.14/0.40  #    Propositional check unsatisfiable : 0
% 0.14/0.40  #    Propositional clauses             : 0
% 0.14/0.40  #    Propositional clauses after purity: 0
% 0.14/0.40  #    Propositional unsat core size     : 0
% 0.14/0.40  #    Propositional preprocessing time  : 0.000
% 0.14/0.40  #    Propositional encoding time       : 0.000
% 0.14/0.40  #    Propositional solver time         : 0.000
% 0.14/0.40  #    Success case prop preproc time    : 0.000
% 0.14/0.40  #    Success case prop encoding time   : 0.000
% 0.14/0.40  #    Success case prop solver time     : 0.000
% 0.14/0.40  # Current number of processed clauses  : 89
% 0.14/0.40  #    Positive orientable unit clauses  : 11
% 0.14/0.40  #    Positive unorientable unit clauses: 0
% 0.14/0.40  #    Negative unit clauses             : 4
% 0.14/0.40  #    Non-unit-clauses                  : 74
% 0.14/0.40  # Current number of unprocessed clauses: 219
% 0.14/0.40  # ...number of literals in the above   : 966
% 0.14/0.40  # Current number of archived formulas  : 0
% 0.14/0.40  # Current number of archived clauses   : 14
% 0.14/0.40  # Clause-clause subsumption calls (NU) : 998
% 0.14/0.40  # Rec. Clause-clause subsumption calls : 759
% 0.14/0.40  # Non-unit clause-clause subsumptions  : 94
% 0.14/0.40  # Unit Clause-clause subsumption calls : 54
% 0.14/0.40  # Rewrite failures with RHS unbound    : 0
% 0.14/0.40  # BW rewrite match attempts            : 6
% 0.14/0.40  # BW rewrite match successes           : 6
% 0.14/0.40  # Condensation attempts                : 0
% 0.14/0.40  # Condensation successes               : 0
% 0.14/0.40  # Termbank termtop insertions          : 9188
% 0.14/0.40  
% 0.14/0.40  # -------------------------------------------------
% 0.14/0.40  # User time                : 0.040 s
% 0.14/0.40  # System time              : 0.004 s
% 0.14/0.40  # Total time               : 0.045 s
% 0.14/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
