%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:16 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 118 expanded)
%              Number of clauses        :   24 (  51 expanded)
%              Number of leaves         :    9 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  129 ( 395 expanded)
%              Number of equality atoms :   24 (  94 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(t205_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(t56_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),X1)
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(t55_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
        & r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(c_0_9,plain,(
    ! [X17,X18,X19,X21,X22,X23,X24,X26] :
      ( ( ~ r2_hidden(X19,X18)
        | r2_hidden(k4_tarski(X19,esk4_3(X17,X18,X19)),X17)
        | X18 != k1_relat_1(X17) )
      & ( ~ r2_hidden(k4_tarski(X21,X22),X17)
        | r2_hidden(X21,X18)
        | X18 != k1_relat_1(X17) )
      & ( ~ r2_hidden(esk5_2(X23,X24),X24)
        | ~ r2_hidden(k4_tarski(esk5_2(X23,X24),X26),X23)
        | X24 = k1_relat_1(X23) )
      & ( r2_hidden(esk5_2(X23,X24),X24)
        | r2_hidden(k4_tarski(esk5_2(X23,X24),esk6_2(X23,X24)),X23)
        | X24 = k1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_11,plain,(
    ! [X34,X35,X36] :
      ( ( ~ r2_hidden(k4_tarski(X34,X35),X36)
        | r2_hidden(X35,k11_relat_1(X36,X34))
        | ~ v1_relat_1(X36) )
      & ( ~ r2_hidden(X35,k11_relat_1(X36,X34))
        | r2_hidden(k4_tarski(X34,X35),X36)
        | ~ v1_relat_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X9,X10,X13,X15,X16] :
      ( ( ~ v1_relat_1(X9)
        | ~ r2_hidden(X10,X9)
        | X10 = k4_tarski(esk1_2(X9,X10),esk2_2(X9,X10)) )
      & ( r2_hidden(esk3_1(X13),X13)
        | v1_relat_1(X13) )
      & ( esk3_1(X13) != k4_tarski(X15,X16)
        | v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,k11_relat_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,negated_conjecture,
    ( v1_relat_1(esk11_0)
    & ( ~ r2_hidden(esk10_0,k1_relat_1(esk11_0))
      | k11_relat_1(esk11_0,esk10_0) = k1_xboole_0 )
    & ( r2_hidden(esk10_0,k1_relat_1(esk11_0))
      | k11_relat_1(esk11_0,esk10_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_19,plain,
    ( v1_relat_1(k11_relat_1(X1,X2))
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_21,plain,(
    ! [X37] :
      ( ~ v1_relat_1(X37)
      | r2_hidden(k4_tarski(esk8_1(X37),esk9_1(X37)),X37)
      | X37 = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).

cnf(c_0_22,negated_conjecture,
    ( k11_relat_1(esk11_0,esk10_0) = k1_xboole_0
    | ~ r2_hidden(esk10_0,k1_relat_1(esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(k11_relat_1(esk11_0,X1))
    | r2_hidden(X1,k1_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_24,plain,(
    ! [X28,X29,X30,X32] :
      ( ( r2_hidden(esk7_3(X28,X29,X30),k2_relat_1(X30))
        | ~ r2_hidden(X28,k10_relat_1(X30,X29))
        | ~ v1_relat_1(X30) )
      & ( r2_hidden(k4_tarski(X28,esk7_3(X28,X29,X30)),X30)
        | ~ r2_hidden(X28,k10_relat_1(X30,X29))
        | ~ v1_relat_1(X30) )
      & ( r2_hidden(esk7_3(X28,X29,X30),X29)
        | ~ r2_hidden(X28,k10_relat_1(X30,X29))
        | ~ v1_relat_1(X30) )
      & ( ~ r2_hidden(X32,k2_relat_1(X30))
        | ~ r2_hidden(k4_tarski(X28,X32),X30)
        | ~ r2_hidden(X32,X29)
        | r2_hidden(X28,k10_relat_1(X30,X29))
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(esk8_1(X1),esk9_1(X1)),X1)
    | X1 = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( k11_relat_1(esk11_0,esk10_0) = k1_xboole_0
    | v1_relat_1(k11_relat_1(esk11_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_27,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_xboole_0(k2_tarski(X6,X7),X8)
      | ~ r2_hidden(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).

fof(c_0_28,plain,(
    ! [X5] : r1_xboole_0(X5,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_29,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,esk7_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k11_relat_1(esk11_0,esk10_0) = k1_xboole_0
    | r2_hidden(k4_tarski(esk8_1(k11_relat_1(esk11_0,esk10_0)),esk9_1(k11_relat_1(esk11_0,esk10_0))),k11_relat_1(esk11_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( ~ r1_xboole_0(k2_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),k11_relat_1(X3,X1))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( k11_relat_1(esk11_0,esk10_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_31]),c_0_20])]),c_0_22])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_37,plain,(
    ! [X33] :
      ( ~ v1_relat_1(X33)
      | k10_relat_1(X33,k2_relat_1(X33)) = k1_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk10_0,k1_relat_1(esk11_0))
    | k11_relat_1(esk11_0,esk10_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(esk10_0,k10_relat_1(esk11_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_20])]),c_0_36])).

cnf(c_0_40,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk10_0,k1_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_35])])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:58:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.46  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.46  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.46  #
% 0.19/0.46  # Preprocessing time       : 0.039 s
% 0.19/0.46  # Presaturation interreduction done
% 0.19/0.46  
% 0.19/0.46  # Proof found!
% 0.19/0.46  # SZS status Theorem
% 0.19/0.46  # SZS output start CNFRefutation
% 0.19/0.46  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.19/0.46  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 0.19/0.46  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 0.19/0.46  fof(t205_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 0.19/0.46  fof(t56_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(![X2, X3]:~(r2_hidden(k4_tarski(X2,X3),X1))=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 0.19/0.46  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.19/0.46  fof(t55_zfmisc_1, axiom, ![X1, X2, X3]:~((r1_xboole_0(k2_tarski(X1,X2),X3)&r2_hidden(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 0.19/0.46  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.46  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.19/0.46  fof(c_0_9, plain, ![X17, X18, X19, X21, X22, X23, X24, X26]:(((~r2_hidden(X19,X18)|r2_hidden(k4_tarski(X19,esk4_3(X17,X18,X19)),X17)|X18!=k1_relat_1(X17))&(~r2_hidden(k4_tarski(X21,X22),X17)|r2_hidden(X21,X18)|X18!=k1_relat_1(X17)))&((~r2_hidden(esk5_2(X23,X24),X24)|~r2_hidden(k4_tarski(esk5_2(X23,X24),X26),X23)|X24=k1_relat_1(X23))&(r2_hidden(esk5_2(X23,X24),X24)|r2_hidden(k4_tarski(esk5_2(X23,X24),esk6_2(X23,X24)),X23)|X24=k1_relat_1(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.19/0.46  cnf(c_0_10, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.46  fof(c_0_11, plain, ![X34, X35, X36]:((~r2_hidden(k4_tarski(X34,X35),X36)|r2_hidden(X35,k11_relat_1(X36,X34))|~v1_relat_1(X36))&(~r2_hidden(X35,k11_relat_1(X36,X34))|r2_hidden(k4_tarski(X34,X35),X36)|~v1_relat_1(X36))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.19/0.46  cnf(c_0_12, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_10])).
% 0.19/0.46  cnf(c_0_13, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.46  fof(c_0_14, plain, ![X9, X10, X13, X15, X16]:((~v1_relat_1(X9)|(~r2_hidden(X10,X9)|X10=k4_tarski(esk1_2(X9,X10),esk2_2(X9,X10))))&((r2_hidden(esk3_1(X13),X13)|v1_relat_1(X13))&(esk3_1(X13)!=k4_tarski(X15,X16)|v1_relat_1(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.19/0.46  fof(c_0_15, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t205_relat_1])).
% 0.19/0.46  cnf(c_0_16, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X3,k11_relat_1(X2,X1))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.46  cnf(c_0_17, plain, (r2_hidden(esk3_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.46  fof(c_0_18, negated_conjecture, (v1_relat_1(esk11_0)&((~r2_hidden(esk10_0,k1_relat_1(esk11_0))|k11_relat_1(esk11_0,esk10_0)=k1_xboole_0)&(r2_hidden(esk10_0,k1_relat_1(esk11_0))|k11_relat_1(esk11_0,esk10_0)!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.19/0.46  cnf(c_0_19, plain, (v1_relat_1(k11_relat_1(X1,X2))|r2_hidden(X2,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.46  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.46  fof(c_0_21, plain, ![X37]:(~v1_relat_1(X37)|(r2_hidden(k4_tarski(esk8_1(X37),esk9_1(X37)),X37)|X37=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).
% 0.19/0.46  cnf(c_0_22, negated_conjecture, (k11_relat_1(esk11_0,esk10_0)=k1_xboole_0|~r2_hidden(esk10_0,k1_relat_1(esk11_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.46  cnf(c_0_23, negated_conjecture, (v1_relat_1(k11_relat_1(esk11_0,X1))|r2_hidden(X1,k1_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.46  fof(c_0_24, plain, ![X28, X29, X30, X32]:((((r2_hidden(esk7_3(X28,X29,X30),k2_relat_1(X30))|~r2_hidden(X28,k10_relat_1(X30,X29))|~v1_relat_1(X30))&(r2_hidden(k4_tarski(X28,esk7_3(X28,X29,X30)),X30)|~r2_hidden(X28,k10_relat_1(X30,X29))|~v1_relat_1(X30)))&(r2_hidden(esk7_3(X28,X29,X30),X29)|~r2_hidden(X28,k10_relat_1(X30,X29))|~v1_relat_1(X30)))&(~r2_hidden(X32,k2_relat_1(X30))|~r2_hidden(k4_tarski(X28,X32),X30)|~r2_hidden(X32,X29)|r2_hidden(X28,k10_relat_1(X30,X29))|~v1_relat_1(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.19/0.46  cnf(c_0_25, plain, (r2_hidden(k4_tarski(esk8_1(X1),esk9_1(X1)),X1)|X1=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.46  cnf(c_0_26, negated_conjecture, (k11_relat_1(esk11_0,esk10_0)=k1_xboole_0|v1_relat_1(k11_relat_1(esk11_0,esk10_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.46  fof(c_0_27, plain, ![X6, X7, X8]:(~r1_xboole_0(k2_tarski(X6,X7),X8)|~r2_hidden(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).
% 0.19/0.46  fof(c_0_28, plain, ![X5]:r1_xboole_0(X5,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.46  cnf(c_0_29, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.46  cnf(c_0_30, plain, (r2_hidden(k4_tarski(X1,esk7_3(X1,X2,X3)),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.46  cnf(c_0_31, negated_conjecture, (k11_relat_1(esk11_0,esk10_0)=k1_xboole_0|r2_hidden(k4_tarski(esk8_1(k11_relat_1(esk11_0,esk10_0)),esk9_1(k11_relat_1(esk11_0,esk10_0))),k11_relat_1(esk11_0,esk10_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.46  cnf(c_0_32, plain, (~r1_xboole_0(k2_tarski(X1,X2),X3)|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.46  cnf(c_0_33, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.46  cnf(c_0_34, plain, (r2_hidden(esk7_3(X1,X2,X3),k11_relat_1(X3,X1))|~v1_relat_1(X3)|~r2_hidden(X1,k10_relat_1(X3,X2))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.46  cnf(c_0_35, negated_conjecture, (k11_relat_1(esk11_0,esk10_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_31]), c_0_20])]), c_0_22])).
% 0.19/0.46  cnf(c_0_36, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.46  fof(c_0_37, plain, ![X33]:(~v1_relat_1(X33)|k10_relat_1(X33,k2_relat_1(X33))=k1_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.19/0.46  cnf(c_0_38, negated_conjecture, (r2_hidden(esk10_0,k1_relat_1(esk11_0))|k11_relat_1(esk11_0,esk10_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.46  cnf(c_0_39, negated_conjecture, (~r2_hidden(esk10_0,k10_relat_1(esk11_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_20])]), c_0_36])).
% 0.19/0.46  cnf(c_0_40, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.46  cnf(c_0_41, negated_conjecture, (r2_hidden(esk10_0,k1_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_35])])).
% 0.19/0.46  cnf(c_0_42, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_20])]), ['proof']).
% 0.19/0.46  # SZS output end CNFRefutation
% 0.19/0.46  # Proof object total steps             : 43
% 0.19/0.46  # Proof object clause steps            : 24
% 0.19/0.46  # Proof object formula steps           : 19
% 0.19/0.46  # Proof object conjectures             : 13
% 0.19/0.46  # Proof object clause conjectures      : 10
% 0.19/0.46  # Proof object formula conjectures     : 3
% 0.19/0.46  # Proof object initial clauses used    : 12
% 0.19/0.46  # Proof object initial formulas used   : 9
% 0.19/0.46  # Proof object generating inferences   : 10
% 0.19/0.46  # Proof object simplifying inferences  : 12
% 0.19/0.46  # Training examples: 0 positive, 0 negative
% 0.19/0.46  # Parsed axioms                        : 9
% 0.19/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.46  # Initial clauses                      : 20
% 0.19/0.46  # Removed in clause preprocessing      : 0
% 0.19/0.46  # Initial clauses in saturation        : 20
% 0.19/0.46  # Processed clauses                    : 724
% 0.19/0.46  # ...of these trivial                  : 1
% 0.19/0.46  # ...subsumed                          : 494
% 0.19/0.46  # ...remaining for further processing  : 229
% 0.19/0.46  # Other redundant clauses eliminated   : 3
% 0.19/0.46  # Clauses deleted for lack of memory   : 0
% 0.19/0.46  # Backward-subsumed                    : 2
% 0.19/0.46  # Backward-rewritten                   : 12
% 0.19/0.46  # Generated clauses                    : 2551
% 0.19/0.46  # ...of the previous two non-trivial   : 2099
% 0.19/0.46  # Contextual simplify-reflections      : 24
% 0.19/0.46  # Paramodulations                      : 2548
% 0.19/0.46  # Factorizations                       : 0
% 0.19/0.46  # Equation resolutions                 : 3
% 0.19/0.46  # Propositional unsat checks           : 0
% 0.19/0.46  #    Propositional check models        : 0
% 0.19/0.46  #    Propositional check unsatisfiable : 0
% 0.19/0.46  #    Propositional clauses             : 0
% 0.19/0.46  #    Propositional clauses after purity: 0
% 0.19/0.46  #    Propositional unsat core size     : 0
% 0.19/0.46  #    Propositional preprocessing time  : 0.000
% 0.19/0.46  #    Propositional encoding time       : 0.000
% 0.19/0.46  #    Propositional solver time         : 0.000
% 0.19/0.46  #    Success case prop preproc time    : 0.000
% 0.19/0.46  #    Success case prop encoding time   : 0.000
% 0.19/0.46  #    Success case prop solver time     : 0.000
% 0.19/0.46  # Current number of processed clauses  : 193
% 0.19/0.46  #    Positive orientable unit clauses  : 8
% 0.19/0.46  #    Positive unorientable unit clauses: 0
% 0.19/0.46  #    Negative unit clauses             : 2
% 0.19/0.46  #    Non-unit-clauses                  : 183
% 0.19/0.46  # Current number of unprocessed clauses: 1399
% 0.19/0.46  # ...number of literals in the above   : 5681
% 0.19/0.46  # Current number of archived formulas  : 0
% 0.19/0.46  # Current number of archived clauses   : 34
% 0.19/0.46  # Clause-clause subsumption calls (NU) : 5730
% 0.19/0.46  # Rec. Clause-clause subsumption calls : 2095
% 0.19/0.46  # Non-unit clause-clause subsumptions  : 111
% 0.19/0.46  # Unit Clause-clause subsumption calls : 64
% 0.19/0.46  # Rewrite failures with RHS unbound    : 0
% 0.19/0.46  # BW rewrite match attempts            : 6
% 0.19/0.46  # BW rewrite match successes           : 6
% 0.19/0.46  # Condensation attempts                : 0
% 0.19/0.46  # Condensation successes               : 0
% 0.19/0.46  # Termbank termtop insertions          : 48104
% 0.19/0.46  
% 0.19/0.46  # -------------------------------------------------
% 0.19/0.46  # User time                : 0.119 s
% 0.19/0.46  # System time              : 0.007 s
% 0.19/0.46  # Total time               : 0.126 s
% 0.19/0.46  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
