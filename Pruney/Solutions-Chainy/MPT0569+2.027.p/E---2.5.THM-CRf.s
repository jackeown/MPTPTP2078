%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:36 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 158 expanded)
%              Number of clauses        :   39 (  72 expanded)
%              Number of leaves         :    8 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  167 ( 620 expanded)
%              Number of equality atoms :   25 (  75 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

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

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

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

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(c_0_8,plain,(
    ! [X13,X14,X16,X17,X18] :
      ( ( r1_xboole_0(X13,X14)
        | r2_hidden(esk2_2(X13,X14),k3_xboole_0(X13,X14)) )
      & ( ~ r2_hidden(X18,k3_xboole_0(X16,X17))
        | ~ r1_xboole_0(X16,X17) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_9,plain,(
    ! [X5,X6] :
      ( ( ~ r1_xboole_0(X5,X6)
        | k3_xboole_0(X5,X6) = k1_xboole_0 )
      & ( k3_xboole_0(X5,X6) != k1_xboole_0
        | r1_xboole_0(X5,X6) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_10,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X33,X34,X35,X37] :
      ( ( r2_hidden(esk7_3(X33,X34,X35),k2_relat_1(X35))
        | ~ r2_hidden(X33,k10_relat_1(X35,X34))
        | ~ v1_relat_1(X35) )
      & ( r2_hidden(k4_tarski(X33,esk7_3(X33,X34,X35)),X35)
        | ~ r2_hidden(X33,k10_relat_1(X35,X34))
        | ~ v1_relat_1(X35) )
      & ( r2_hidden(esk7_3(X33,X34,X35),X34)
        | ~ r2_hidden(X33,k10_relat_1(X35,X34))
        | ~ v1_relat_1(X35) )
      & ( ~ r2_hidden(X37,k2_relat_1(X35))
        | ~ r2_hidden(k4_tarski(X33,X37),X35)
        | ~ r2_hidden(X37,X34)
        | r2_hidden(X33,k10_relat_1(X35,X34))
        | ~ v1_relat_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

fof(c_0_13,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_xboole_0(X7,X8) )
      & ( r2_hidden(esk1_2(X7,X8),X8)
        | r1_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X19] :
      ( X19 = k1_xboole_0
      | r2_hidden(esk3_1(X19),X19) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X21] : r1_xboole_0(X21,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_19,plain,(
    ! [X22,X23,X24,X26,X27,X28,X29,X31] :
      ( ( ~ r2_hidden(X24,X23)
        | r2_hidden(k4_tarski(esk4_3(X22,X23,X24),X24),X22)
        | X23 != k2_relat_1(X22) )
      & ( ~ r2_hidden(k4_tarski(X27,X26),X22)
        | r2_hidden(X26,X23)
        | X23 != k2_relat_1(X22) )
      & ( ~ r2_hidden(esk5_2(X28,X29),X29)
        | ~ r2_hidden(k4_tarski(X31,esk5_2(X28,X29)),X28)
        | X29 = k2_relat_1(X28) )
      & ( r2_hidden(esk5_2(X28,X29),X29)
        | r2_hidden(k4_tarski(esk6_2(X28,X29),esk5_2(X28,X29)),X28)
        | X29 = k2_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,k1_xboole_0))
    | ~ r1_xboole_0(X3,X4) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r1_xboole_0(k1_xboole_0,X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_17])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

cnf(c_0_26,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(esk7_3(X2,X3,X1),X4)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ r1_xboole_0(X4,X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_15])).

cnf(c_0_28,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_31,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & ( k10_relat_1(esk9_0,esk8_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk9_0),esk8_0) )
    & ( k10_relat_1(esk9_0,esk8_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk9_0),esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_32,plain,
    ( r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(esk4_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ r1_xboole_0(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_22])).

cnf(c_0_41,negated_conjecture,
    ( k10_relat_1(esk9_0,esk8_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk9_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ r1_xboole_0(X3,X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( k10_relat_1(esk9_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( r2_hidden(esk4_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( k10_relat_1(esk9_0,esk8_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_37])])).

cnf(c_0_46,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_37]),c_0_30])])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk9_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_37])]),c_0_46])).

cnf(c_0_48,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_17])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(X1,k2_relat_1(esk9_0))
    | ~ r2_hidden(esk1_2(X1,k2_relat_1(esk9_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( k10_relat_1(esk9_0,esk8_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk9_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r1_xboole_0(esk8_0,k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_17])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(esk9_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_45])])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.46  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.46  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.46  #
% 0.19/0.46  # Preprocessing time       : 0.028 s
% 0.19/0.46  # Presaturation interreduction done
% 0.19/0.46  
% 0.19/0.46  # Proof found!
% 0.19/0.46  # SZS status Theorem
% 0.19/0.46  # SZS output start CNFRefutation
% 0.19/0.46  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.46  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.19/0.46  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.19/0.46  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.46  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.46  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.46  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.19/0.46  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 0.19/0.46  fof(c_0_8, plain, ![X13, X14, X16, X17, X18]:((r1_xboole_0(X13,X14)|r2_hidden(esk2_2(X13,X14),k3_xboole_0(X13,X14)))&(~r2_hidden(X18,k3_xboole_0(X16,X17))|~r1_xboole_0(X16,X17))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.46  fof(c_0_9, plain, ![X5, X6]:((~r1_xboole_0(X5,X6)|k3_xboole_0(X5,X6)=k1_xboole_0)&(k3_xboole_0(X5,X6)!=k1_xboole_0|r1_xboole_0(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.19/0.46  cnf(c_0_10, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.46  cnf(c_0_11, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.46  fof(c_0_12, plain, ![X33, X34, X35, X37]:((((r2_hidden(esk7_3(X33,X34,X35),k2_relat_1(X35))|~r2_hidden(X33,k10_relat_1(X35,X34))|~v1_relat_1(X35))&(r2_hidden(k4_tarski(X33,esk7_3(X33,X34,X35)),X35)|~r2_hidden(X33,k10_relat_1(X35,X34))|~v1_relat_1(X35)))&(r2_hidden(esk7_3(X33,X34,X35),X34)|~r2_hidden(X33,k10_relat_1(X35,X34))|~v1_relat_1(X35)))&(~r2_hidden(X37,k2_relat_1(X35))|~r2_hidden(k4_tarski(X33,X37),X35)|~r2_hidden(X37,X34)|r2_hidden(X33,k10_relat_1(X35,X34))|~v1_relat_1(X35))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.19/0.46  fof(c_0_13, plain, ![X7, X8, X10, X11, X12]:(((r2_hidden(esk1_2(X7,X8),X7)|r1_xboole_0(X7,X8))&(r2_hidden(esk1_2(X7,X8),X8)|r1_xboole_0(X7,X8)))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|~r1_xboole_0(X10,X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.46  cnf(c_0_14, plain, (~r2_hidden(X1,k1_xboole_0)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.46  cnf(c_0_15, plain, (r2_hidden(esk7_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.46  fof(c_0_16, plain, ![X19]:(X19=k1_xboole_0|r2_hidden(esk3_1(X19),X19)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.46  cnf(c_0_17, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.46  fof(c_0_18, plain, ![X21]:r1_xboole_0(X21,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.46  fof(c_0_19, plain, ![X22, X23, X24, X26, X27, X28, X29, X31]:(((~r2_hidden(X24,X23)|r2_hidden(k4_tarski(esk4_3(X22,X23,X24),X24),X22)|X23!=k2_relat_1(X22))&(~r2_hidden(k4_tarski(X27,X26),X22)|r2_hidden(X26,X23)|X23!=k2_relat_1(X22)))&((~r2_hidden(esk5_2(X28,X29),X29)|~r2_hidden(k4_tarski(X31,esk5_2(X28,X29)),X28)|X29=k2_relat_1(X28))&(r2_hidden(esk5_2(X28,X29),X29)|r2_hidden(k4_tarski(esk6_2(X28,X29),esk5_2(X28,X29)),X28)|X29=k2_relat_1(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.19/0.46  cnf(c_0_20, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.46  cnf(c_0_21, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,k1_xboole_0))|~r1_xboole_0(X3,X4)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.46  cnf(c_0_22, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.46  cnf(c_0_23, plain, (r1_xboole_0(k1_xboole_0,X1)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_14, c_0_17])).
% 0.19/0.46  cnf(c_0_24, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.46  fof(c_0_25, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.19/0.46  cnf(c_0_26, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.46  cnf(c_0_27, plain, (~v1_relat_1(X1)|~r2_hidden(esk7_3(X2,X3,X1),X4)|~r2_hidden(X2,k10_relat_1(X1,X3))|~r1_xboole_0(X4,X3)), inference(spm,[status(thm)],[c_0_20, c_0_15])).
% 0.19/0.46  cnf(c_0_28, plain, (r2_hidden(esk7_3(X1,X2,X3),k2_relat_1(X3))|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.46  cnf(c_0_29, plain, (k10_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.46  cnf(c_0_30, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.46  fof(c_0_31, negated_conjecture, (v1_relat_1(esk9_0)&((k10_relat_1(esk9_0,esk8_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk9_0),esk8_0))&(k10_relat_1(esk9_0,esk8_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk9_0),esk8_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.19/0.46  cnf(c_0_32, plain, (r2_hidden(X3,k10_relat_1(X2,X4))|~r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.46  cnf(c_0_33, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_26])).
% 0.19/0.46  cnf(c_0_34, plain, (r2_hidden(k4_tarski(esk4_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.46  cnf(c_0_35, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,X3))|~r1_xboole_0(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.46  cnf(c_0_36, plain, (k10_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.46  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.46  cnf(c_0_38, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.46  cnf(c_0_39, plain, (r2_hidden(k4_tarski(esk4_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_34])).
% 0.19/0.46  cnf(c_0_40, plain, (k10_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_35, c_0_22])).
% 0.19/0.46  cnf(c_0_41, negated_conjecture, (k10_relat_1(esk9_0,esk8_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk9_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.46  cnf(c_0_42, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,X3))|~r1_xboole_0(X3,X3)), inference(spm,[status(thm)],[c_0_27, c_0_15])).
% 0.19/0.46  cnf(c_0_43, negated_conjecture, (k10_relat_1(esk9_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.46  cnf(c_0_44, plain, (r2_hidden(esk4_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.46  cnf(c_0_45, negated_conjecture, (k10_relat_1(esk9_0,esk8_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_37])])).
% 0.19/0.46  cnf(c_0_46, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_37]), c_0_30])])).
% 0.19/0.46  cnf(c_0_47, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk9_0))|~r2_hidden(X1,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_37])]), c_0_46])).
% 0.19/0.46  cnf(c_0_48, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.46  cnf(c_0_49, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_20, c_0_17])).
% 0.19/0.46  cnf(c_0_50, negated_conjecture, (r1_xboole_0(X1,k2_relat_1(esk9_0))|~r2_hidden(esk1_2(X1,k2_relat_1(esk9_0)),esk8_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.46  cnf(c_0_51, negated_conjecture, (k10_relat_1(esk9_0,esk8_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk9_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.46  cnf(c_0_52, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_49, c_0_48])).
% 0.19/0.46  cnf(c_0_53, negated_conjecture, (r1_xboole_0(esk8_0,k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_50, c_0_17])).
% 0.19/0.46  cnf(c_0_54, negated_conjecture, (~r1_xboole_0(k2_relat_1(esk9_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_45])])).
% 0.19/0.46  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), ['proof']).
% 0.19/0.46  # SZS output end CNFRefutation
% 0.19/0.46  # Proof object total steps             : 56
% 0.19/0.46  # Proof object clause steps            : 39
% 0.19/0.46  # Proof object formula steps           : 17
% 0.19/0.46  # Proof object conjectures             : 14
% 0.19/0.46  # Proof object clause conjectures      : 11
% 0.19/0.46  # Proof object formula conjectures     : 3
% 0.19/0.46  # Proof object initial clauses used    : 15
% 0.19/0.46  # Proof object initial formulas used   : 8
% 0.19/0.46  # Proof object generating inferences   : 20
% 0.19/0.46  # Proof object simplifying inferences  : 14
% 0.19/0.46  # Training examples: 0 positive, 0 negative
% 0.19/0.46  # Parsed axioms                        : 8
% 0.19/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.46  # Initial clauses                      : 20
% 0.19/0.46  # Removed in clause preprocessing      : 0
% 0.19/0.46  # Initial clauses in saturation        : 20
% 0.19/0.46  # Processed clauses                    : 1592
% 0.19/0.46  # ...of these trivial                  : 0
% 0.19/0.46  # ...subsumed                          : 1288
% 0.19/0.46  # ...remaining for further processing  : 304
% 0.19/0.46  # Other redundant clauses eliminated   : 2
% 0.19/0.46  # Clauses deleted for lack of memory   : 0
% 0.19/0.46  # Backward-subsumed                    : 12
% 0.19/0.46  # Backward-rewritten                   : 6
% 0.19/0.46  # Generated clauses                    : 4881
% 0.19/0.46  # ...of the previous two non-trivial   : 4432
% 0.19/0.46  # Contextual simplify-reflections      : 1
% 0.19/0.46  # Paramodulations                      : 4877
% 0.19/0.46  # Factorizations                       : 2
% 0.19/0.46  # Equation resolutions                 : 2
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
% 0.19/0.46  # Current number of processed clauses  : 264
% 0.19/0.46  #    Positive orientable unit clauses  : 7
% 0.19/0.46  #    Positive unorientable unit clauses: 0
% 0.19/0.46  #    Negative unit clauses             : 2
% 0.19/0.46  #    Non-unit-clauses                  : 255
% 0.19/0.46  # Current number of unprocessed clauses: 2826
% 0.19/0.46  # ...number of literals in the above   : 9443
% 0.19/0.46  # Current number of archived formulas  : 0
% 0.19/0.46  # Current number of archived clauses   : 38
% 0.19/0.46  # Clause-clause subsumption calls (NU) : 10346
% 0.19/0.46  # Rec. Clause-clause subsumption calls : 6845
% 0.19/0.46  # Non-unit clause-clause subsumptions  : 688
% 0.19/0.46  # Unit Clause-clause subsumption calls : 27
% 0.19/0.46  # Rewrite failures with RHS unbound    : 0
% 0.19/0.46  # BW rewrite match attempts            : 3
% 0.19/0.46  # BW rewrite match successes           : 3
% 0.19/0.46  # Condensation attempts                : 0
% 0.19/0.46  # Condensation successes               : 0
% 0.19/0.46  # Termbank termtop insertions          : 74331
% 0.19/0.46  
% 0.19/0.46  # -------------------------------------------------
% 0.19/0.46  # User time                : 0.110 s
% 0.19/0.46  # System time              : 0.008 s
% 0.19/0.46  # Total time               : 0.118 s
% 0.19/0.46  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
