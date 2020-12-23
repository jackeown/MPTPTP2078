%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:39 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 317 expanded)
%              Number of clauses        :   49 ( 143 expanded)
%              Number of leaves         :    8 (  78 expanded)
%              Depth                    :   21
%              Number of atoms          :  185 (1173 expanded)
%              Number of equality atoms :   19 ( 100 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_xboole_0(X1,X2)
              & X1 != X2
              & ~ r2_xboole_0(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_ordinal1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(s1_xboole_0__e3_53__ordinal1,axiom,(
    ! [X1] :
    ? [X2] :
    ! [X3] :
      ( r2_hidden(X3,X2)
    <=> ( r2_hidden(X3,X1)
        & v3_ordinal1(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e3_53__ordinal1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_ordinal1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & r2_hidden(X2,X3)
        & r2_hidden(X3,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_ordinal1)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ~ ( ~ r2_xboole_0(X1,X2)
                & X1 != X2
                & ~ r2_xboole_0(X2,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_ordinal1])).

fof(c_0_9,plain,(
    ! [X24,X25] :
      ( ~ v3_ordinal1(X24)
      | ~ v3_ordinal1(X25)
      | r2_hidden(X24,X25)
      | X24 = X25
      | r2_hidden(X25,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

fof(c_0_10,negated_conjecture,
    ( v3_ordinal1(esk3_0)
    & v3_ordinal1(esk4_0)
    & ~ r2_xboole_0(esk3_0,esk4_0)
    & esk3_0 != esk4_0
    & ~ r2_xboole_0(esk4_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X18,X20,X21] :
      ( ( r2_hidden(X20,X18)
        | ~ r2_hidden(X20,esk2_1(X18)) )
      & ( v3_ordinal1(X20)
        | ~ r2_hidden(X20,esk2_1(X18)) )
      & ( ~ r2_hidden(X21,X18)
        | ~ v3_ordinal1(X21)
        | r2_hidden(X21,esk2_1(X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[s1_xboole_0__e3_53__ordinal1])])])])])])).

fof(c_0_14,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_15,plain,(
    ! [X26,X27,X28] :
      ( ~ r2_hidden(X26,X27)
      | ~ r2_hidden(X27,X28)
      | ~ r2_hidden(X28,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_ordinal1])])).

cnf(c_0_16,negated_conjecture,
    ( X1 = esk4_0
    | r2_hidden(esk4_0,X1)
    | r2_hidden(X1,esk4_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk2_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r2_hidden(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk2_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( v3_ordinal1(esk1_2(esk2_1(X1),X2))
    | r1_tarski(esk2_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( r1_tarski(esk2_1(X1),X2)
    | r2_hidden(esk1_2(esk2_1(X1),X2),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_20])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( esk1_2(esk2_1(X1),X2) = esk4_0
    | r1_tarski(esk2_1(X1),X2)
    | r2_hidden(esk1_2(esk2_1(X1),X2),esk4_0)
    | r2_hidden(esk4_0,esk1_2(esk2_1(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,esk2_1(X2))
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_30,plain,(
    ! [X22,X23] :
      ( ~ v3_ordinal1(X23)
      | ~ r2_hidden(X22,X23)
      | v3_ordinal1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk2_1(esk3_0),X1)
    | r2_hidden(esk4_0,esk3_0)
    | ~ r2_hidden(esk4_0,esk1_2(esk2_1(esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( esk1_2(esk2_1(X1),esk4_0) = esk4_0
    | r1_tarski(esk2_1(X1),esk4_0)
    | r2_hidden(esk4_0,esk1_2(esk2_1(X1),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,esk2_1(X2))
    | ~ v3_ordinal1(esk1_2(X1,esk2_1(X2)))
    | ~ r2_hidden(esk1_2(X1,esk2_1(X2)),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_29])).

cnf(c_0_34,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( esk1_2(esk2_1(esk3_0),esk4_0) = esk4_0
    | r1_tarski(esk2_1(esk3_0),esk4_0)
    | r2_hidden(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,esk2_1(X1))
    | ~ v3_ordinal1(esk1_2(X1,esk2_1(X1))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_20])).

cnf(c_0_37,plain,
    ( v3_ordinal1(esk1_2(X1,X2))
    | r1_tarski(X1,X2)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_20])).

cnf(c_0_38,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk2_1(esk3_0),esk4_0)
    | r2_hidden(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_35])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,esk2_1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk2_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,esk2_1(X2))
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_40])).

fof(c_0_43,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | ~ r2_xboole_0(X12,X13) )
      & ( X12 != X13
        | ~ r2_xboole_0(X12,X13) )
      & ( ~ r1_tarski(X12,X13)
        | X12 = X13
        | r2_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_17])])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_46,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | r2_hidden(esk1_2(esk3_0,X1),esk4_0)
    | r2_hidden(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_18])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_47]),c_0_48])).

cnf(c_0_50,negated_conjecture,
    ( X1 = esk3_0
    | r2_hidden(esk3_0,X1)
    | r2_hidden(X1,esk3_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_17])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( esk1_2(esk2_1(X1),X2) = esk3_0
    | r1_tarski(esk2_1(X1),X2)
    | r2_hidden(esk1_2(esk2_1(X1),X2),esk3_0)
    | r2_hidden(esk3_0,esk1_2(esk2_1(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_24])).

fof(c_0_53,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,X5)
      | ~ r2_hidden(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk2_1(esk4_0),X1)
    | ~ r2_hidden(esk3_0,esk1_2(esk2_1(esk4_0),X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_26])).

cnf(c_0_55,negated_conjecture,
    ( esk1_2(esk2_1(X1),esk3_0) = esk3_0
    | r1_tarski(esk2_1(X1),esk3_0)
    | r2_hidden(esk3_0,esk1_2(esk2_1(X1),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_52])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( esk1_2(esk2_1(esk4_0),esk3_0) = esk3_0
    | r1_tarski(esk2_1(esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk2_1(esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_57]),c_0_58])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_59])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_42]),c_0_12])])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_xboole_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r2_hidden(esk1_2(X1,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_46]),c_0_18])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_20]),c_0_64]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t50_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_xboole_0(X1,X2))&X1!=X2)&~(r2_xboole_0(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_ordinal1)).
% 0.19/0.38  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 0.19/0.38  fof(s1_xboole_0__e3_53__ordinal1, axiom, ![X1]:?[X2]:![X3]:(r2_hidden(X3,X2)<=>(r2_hidden(X3,X1)&v3_ordinal1(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s1_xboole_0__e3_53__ordinal1)).
% 0.19/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.38  fof(t3_ordinal1, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&r2_hidden(X2,X3))&r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_ordinal1)).
% 0.19/0.38  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 0.19/0.38  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.19/0.38  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.19/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_xboole_0(X1,X2))&X1!=X2)&~(r2_xboole_0(X2,X1))))))), inference(assume_negation,[status(cth)],[t50_ordinal1])).
% 0.19/0.38  fof(c_0_9, plain, ![X24, X25]:(~v3_ordinal1(X24)|(~v3_ordinal1(X25)|(r2_hidden(X24,X25)|X24=X25|r2_hidden(X25,X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 0.19/0.38  fof(c_0_10, negated_conjecture, (v3_ordinal1(esk3_0)&(v3_ordinal1(esk4_0)&((~r2_xboole_0(esk3_0,esk4_0)&esk3_0!=esk4_0)&~r2_xboole_0(esk4_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.19/0.38  cnf(c_0_11, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_12, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  fof(c_0_13, plain, ![X18, X20, X21]:(((r2_hidden(X20,X18)|~r2_hidden(X20,esk2_1(X18)))&(v3_ordinal1(X20)|~r2_hidden(X20,esk2_1(X18))))&(~r2_hidden(X21,X18)|~v3_ordinal1(X21)|r2_hidden(X21,esk2_1(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[s1_xboole_0__e3_53__ordinal1])])])])])])).
% 0.19/0.38  fof(c_0_14, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.38  fof(c_0_15, plain, ![X26, X27, X28]:(~r2_hidden(X26,X27)|~r2_hidden(X27,X28)|~r2_hidden(X28,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_ordinal1])])).
% 0.19/0.38  cnf(c_0_16, negated_conjecture, (X1=esk4_0|r2_hidden(esk4_0,X1)|r2_hidden(X1,esk4_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (v3_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_19, plain, (v3_ordinal1(X1)|~r2_hidden(X1,esk2_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_21, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r2_hidden(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.19/0.38  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,esk2_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_24, plain, (v3_ordinal1(esk1_2(esk2_1(X1),X2))|r1_tarski(esk2_1(X1),X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|~r2_hidden(X1,esk3_0)|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.38  cnf(c_0_26, plain, (r1_tarski(esk2_1(X1),X2)|r2_hidden(esk1_2(esk2_1(X1),X2),X1)), inference(spm,[status(thm)],[c_0_23, c_0_20])).
% 0.19/0.38  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (esk1_2(esk2_1(X1),X2)=esk4_0|r1_tarski(esk2_1(X1),X2)|r2_hidden(esk1_2(esk2_1(X1),X2),esk4_0)|r2_hidden(esk4_0,esk1_2(esk2_1(X1),X2))), inference(spm,[status(thm)],[c_0_16, c_0_24])).
% 0.19/0.38  cnf(c_0_29, plain, (r2_hidden(X1,esk2_1(X2))|~r2_hidden(X1,X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  fof(c_0_30, plain, ![X22, X23]:(~v3_ordinal1(X23)|(~r2_hidden(X22,X23)|v3_ordinal1(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (r1_tarski(esk2_1(esk3_0),X1)|r2_hidden(esk4_0,esk3_0)|~r2_hidden(esk4_0,esk1_2(esk2_1(esk3_0),X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (esk1_2(esk2_1(X1),esk4_0)=esk4_0|r1_tarski(esk2_1(X1),esk4_0)|r2_hidden(esk4_0,esk1_2(esk2_1(X1),esk4_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.38  cnf(c_0_33, plain, (r1_tarski(X1,esk2_1(X2))|~v3_ordinal1(esk1_2(X1,esk2_1(X2)))|~r2_hidden(esk1_2(X1,esk2_1(X2)),X2)), inference(spm,[status(thm)],[c_0_27, c_0_29])).
% 0.19/0.38  cnf(c_0_34, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (esk1_2(esk2_1(esk3_0),esk4_0)=esk4_0|r1_tarski(esk2_1(esk3_0),esk4_0)|r2_hidden(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.38  cnf(c_0_36, plain, (r1_tarski(X1,esk2_1(X1))|~v3_ordinal1(esk1_2(X1,esk2_1(X1)))), inference(spm,[status(thm)],[c_0_33, c_0_20])).
% 0.19/0.38  cnf(c_0_37, plain, (v3_ordinal1(esk1_2(X1,X2))|r1_tarski(X1,X2)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_34, c_0_20])).
% 0.19/0.38  cnf(c_0_38, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (r1_tarski(esk2_1(esk3_0),esk4_0)|r2_hidden(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_35])).
% 0.19/0.38  cnf(c_0_40, plain, (r1_tarski(X1,esk2_1(X1))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk2_1(esk3_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.38  cnf(c_0_42, plain, (r2_hidden(X1,esk2_1(X2))|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_38, c_0_40])).
% 0.19/0.38  fof(c_0_43, plain, ![X12, X13]:(((r1_tarski(X12,X13)|~r2_xboole_0(X12,X13))&(X12!=X13|~r2_xboole_0(X12,X13)))&(~r1_tarski(X12,X13)|X12=X13|r2_xboole_0(X12,X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_17])])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (~r2_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_46, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (r1_tarski(esk3_0,X1)|r2_hidden(esk1_2(esk3_0,X1),esk4_0)|r2_hidden(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_44, c_0_20])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_18])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (r2_hidden(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_47]), c_0_48])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (X1=esk3_0|r2_hidden(esk3_0,X1)|r2_hidden(X1,esk3_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_11, c_0_17])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (~r2_hidden(X1,esk4_0)|~r2_hidden(esk3_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_49])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (esk1_2(esk2_1(X1),X2)=esk3_0|r1_tarski(esk2_1(X1),X2)|r2_hidden(esk1_2(esk2_1(X1),X2),esk3_0)|r2_hidden(esk3_0,esk1_2(esk2_1(X1),X2))), inference(spm,[status(thm)],[c_0_50, c_0_24])).
% 0.19/0.38  fof(c_0_53, plain, ![X4, X5]:(~r2_hidden(X4,X5)|~r2_hidden(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (r1_tarski(esk2_1(esk4_0),X1)|~r2_hidden(esk3_0,esk1_2(esk2_1(esk4_0),X1))), inference(spm,[status(thm)],[c_0_51, c_0_26])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (esk1_2(esk2_1(X1),esk3_0)=esk3_0|r1_tarski(esk2_1(X1),esk3_0)|r2_hidden(esk3_0,esk1_2(esk2_1(X1),esk3_0))), inference(spm,[status(thm)],[c_0_27, c_0_52])).
% 0.19/0.38  cnf(c_0_56, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (esk1_2(esk2_1(esk4_0),esk3_0)=esk3_0|r1_tarski(esk2_1(esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (~r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_49])).
% 0.19/0.38  cnf(c_0_59, negated_conjecture, (r1_tarski(esk2_1(esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_57]), c_0_58])).
% 0.19/0.38  cnf(c_0_60, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk2_1(esk4_0))), inference(spm,[status(thm)],[c_0_38, c_0_59])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_42]), c_0_12])])).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (~r2_xboole_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (r1_tarski(X1,esk3_0)|~r2_hidden(esk1_2(X1,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_61])).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, (~r1_tarski(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_46]), c_0_18])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_20]), c_0_64]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 66
% 0.19/0.38  # Proof object clause steps            : 49
% 0.19/0.38  # Proof object formula steps           : 17
% 0.19/0.38  # Proof object conjectures             : 34
% 0.19/0.38  # Proof object clause conjectures      : 31
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 16
% 0.19/0.38  # Proof object initial formulas used   : 8
% 0.19/0.38  # Proof object generating inferences   : 33
% 0.19/0.38  # Proof object simplifying inferences  : 10
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 10
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 22
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 22
% 0.19/0.38  # Processed clauses                    : 151
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 41
% 0.19/0.38  # ...remaining for further processing  : 110
% 0.19/0.38  # Other redundant clauses eliminated   : 1
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 3
% 0.19/0.38  # Backward-rewritten                   : 10
% 0.19/0.38  # Generated clauses                    : 414
% 0.19/0.38  # ...of the previous two non-trivial   : 365
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 413
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 1
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 96
% 0.19/0.38  #    Positive orientable unit clauses  : 11
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 7
% 0.19/0.38  #    Non-unit-clauses                  : 78
% 0.19/0.38  # Current number of unprocessed clauses: 201
% 0.19/0.38  # ...number of literals in the above   : 748
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 13
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 2198
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 1111
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 42
% 0.19/0.38  # Unit Clause-clause subsumption calls : 170
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 25
% 0.19/0.38  # BW rewrite match successes           : 2
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 8569
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.040 s
% 0.19/0.38  # System time              : 0.003 s
% 0.19/0.38  # Total time               : 0.043 s
% 0.19/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
