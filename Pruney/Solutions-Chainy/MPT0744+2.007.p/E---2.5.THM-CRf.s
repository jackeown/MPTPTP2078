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
% DateTime   : Thu Dec  3 10:56:23 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 508 expanded)
%              Number of clauses        :   40 ( 224 expanded)
%              Number of leaves         :   14 ( 121 expanded)
%              Depth                    :   13
%              Number of atoms          :  181 (1569 expanded)
%              Number of equality atoms :   27 ( 228 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t21_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_xboole_0(X1,X2)
           => r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X1,k1_ordinal1(X2))
            <=> r1_ordinal1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_ordinal1])).

fof(c_0_15,plain,(
    ! [X23] : k1_ordinal1(X23) = k2_xboole_0(X23,k1_tarski(X23)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_16,plain,(
    ! [X18] : k2_tarski(X18,X18) = k1_tarski(X18) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_17,negated_conjecture,
    ( v3_ordinal1(esk2_0)
    & v3_ordinal1(esk3_0)
    & ( ~ r2_hidden(esk2_0,k1_ordinal1(esk3_0))
      | ~ r1_ordinal1(esk2_0,esk3_0) )
    & ( r2_hidden(esk2_0,k1_ordinal1(esk3_0))
      | r1_ordinal1(esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_18,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X10,X9)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X14)
        | r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k2_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_21,plain,(
    ! [X29,X30] :
      ( ~ v3_ordinal1(X29)
      | ~ v3_ordinal1(X30)
      | r1_ordinal1(X29,X30)
      | r2_hidden(X30,X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k1_ordinal1(esk3_0))
    | ~ r1_ordinal1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_27,plain,(
    ! [X21] : k3_tarski(k1_tarski(X21)) = X21 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk2_0,k1_ordinal1(esk3_0))
    | r1_ordinal1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_ordinal1(esk2_0,esk3_0)
    | ~ r2_hidden(esk2_0,k2_xboole_0(esk3_0,k2_tarski(esk3_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( r1_ordinal1(X1,esk3_0)
    | r2_hidden(esk3_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( v3_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_34,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

fof(c_0_35,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(X19,X20)
      | r1_tarski(X19,k3_tarski(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_36,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( r1_ordinal1(esk2_0,esk3_0)
    | r2_hidden(esk2_0,k2_xboole_0(esk3_0,k2_tarski(esk3_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_23])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_ordinal1(esk2_0,esk3_0)
    | ~ r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( r1_ordinal1(esk2_0,esk3_0)
    | r2_hidden(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( k3_tarski(k2_tarski(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_36,c_0_19])).

cnf(c_0_44,negated_conjecture,
    ( r1_ordinal1(esk2_0,esk3_0)
    | r2_hidden(esk2_0,k2_tarski(esk3_0,esk3_0))
    | r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

fof(c_0_46,plain,(
    ! [X24,X25] :
      ( ( ~ r1_ordinal1(X24,X25)
        | r1_tarski(X24,X25)
        | ~ v3_ordinal1(X24)
        | ~ v3_ordinal1(X25) )
      & ( ~ r1_tarski(X24,X25)
        | r1_ordinal1(X24,X25)
        | ~ v3_ordinal1(X24)
        | ~ v3_ordinal1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r1_ordinal1(esk2_0,esk3_0)
    | r2_hidden(esk2_0,k2_tarski(esk3_0,esk3_0)) ),
    inference(sr,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_49,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | ~ r2_xboole_0(X16,X17) )
      & ( X16 != X17
        | ~ r2_xboole_0(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | X16 = X17
        | r2_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( r1_ordinal1(esk2_0,esk3_0)
    | r1_tarski(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_52,plain,(
    ! [X31,X32] :
      ( ~ r2_hidden(X31,X32)
      | ~ r1_tarski(X32,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_53,plain,(
    ! [X27,X28] :
      ( ~ v1_ordinal1(X27)
      | ~ v3_ordinal1(X28)
      | ~ r2_xboole_0(X27,X28)
      | r2_hidden(X27,X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).

cnf(c_0_54,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_26]),c_0_33])])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( esk3_0 = esk2_0
    | r2_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_59,plain,(
    ! [X22] :
      ( ( v1_ordinal1(X22)
        | ~ v3_ordinal1(X22) )
      & ( v2_ordinal1(X22)
        | ~ v3_ordinal1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

fof(c_0_60,plain,(
    ! [X26] : r2_hidden(X26,k1_ordinal1(X26)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( esk3_0 = esk2_0
    | ~ v1_ordinal1(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_26])]),c_0_45])).

cnf(c_0_63,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( r1_ordinal1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[c_0_40,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( esk3_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_33])])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k2_tarski(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_64,c_0_23])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_65])]),c_0_66]),c_0_66]),c_0_66]),c_0_67])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:47:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.13/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.041 s
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t34_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 0.13/0.39  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.13/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.39  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.13/0.39  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.13/0.39  fof(t31_zfmisc_1, axiom, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 0.13/0.39  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.13/0.39  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.13/0.39  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.13/0.39  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.13/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.13/0.39  fof(t21_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_xboole_0(X1,X2)=>r2_hidden(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 0.13/0.39  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 0.13/0.39  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 0.13/0.39  fof(c_0_14, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2))))), inference(assume_negation,[status(cth)],[t34_ordinal1])).
% 0.13/0.39  fof(c_0_15, plain, ![X23]:k1_ordinal1(X23)=k2_xboole_0(X23,k1_tarski(X23)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.13/0.39  fof(c_0_16, plain, ![X18]:k2_tarski(X18,X18)=k1_tarski(X18), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.39  fof(c_0_17, negated_conjecture, (v3_ordinal1(esk2_0)&(v3_ordinal1(esk3_0)&((~r2_hidden(esk2_0,k1_ordinal1(esk3_0))|~r1_ordinal1(esk2_0,esk3_0))&(r2_hidden(esk2_0,k1_ordinal1(esk3_0))|r1_ordinal1(esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.13/0.39  cnf(c_0_18, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_19, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  fof(c_0_20, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X10,X9)|(r2_hidden(X10,X7)|r2_hidden(X10,X8))|X9!=k2_xboole_0(X7,X8))&((~r2_hidden(X11,X7)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))&(~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))))&(((~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13)))&(r2_hidden(esk1_3(X12,X13,X14),X14)|(r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k2_xboole_0(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.13/0.39  fof(c_0_21, plain, ![X29, X30]:(~v3_ordinal1(X29)|(~v3_ordinal1(X30)|(r1_ordinal1(X29,X30)|r2_hidden(X30,X29)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (~r2_hidden(esk2_0,k1_ordinal1(esk3_0))|~r1_ordinal1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_23, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.39  cnf(c_0_24, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_25, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_26, negated_conjecture, (v3_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  fof(c_0_27, plain, ![X21]:k3_tarski(k1_tarski(X21))=X21, inference(variable_rename,[status(thm)],[t31_zfmisc_1])).
% 0.13/0.39  cnf(c_0_28, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_29, negated_conjecture, (r2_hidden(esk2_0,k1_ordinal1(esk3_0))|r1_ordinal1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (~r1_ordinal1(esk2_0,esk3_0)|~r2_hidden(esk2_0,k2_xboole_0(esk3_0,k2_tarski(esk3_0,esk3_0)))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.39  cnf(c_0_31, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, (r1_ordinal1(X1,esk3_0)|r2_hidden(esk3_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (v3_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  fof(c_0_34, plain, ![X5, X6]:(~r2_hidden(X5,X6)|~r2_hidden(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.13/0.39  fof(c_0_35, plain, ![X19, X20]:(~r2_hidden(X19,X20)|r1_tarski(X19,k3_tarski(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.13/0.39  cnf(c_0_36, plain, (k3_tarski(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.39  cnf(c_0_37, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_28])).
% 0.13/0.39  cnf(c_0_38, negated_conjecture, (r1_ordinal1(esk2_0,esk3_0)|r2_hidden(esk2_0,k2_xboole_0(esk3_0,k2_tarski(esk3_0,esk3_0)))), inference(rw,[status(thm)],[c_0_29, c_0_23])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (~r1_ordinal1(esk2_0,esk3_0)|~r2_hidden(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, (r1_ordinal1(esk2_0,esk3_0)|r2_hidden(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.39  cnf(c_0_41, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.39  cnf(c_0_42, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.39  cnf(c_0_43, plain, (k3_tarski(k2_tarski(X1,X1))=X1), inference(rw,[status(thm)],[c_0_36, c_0_19])).
% 0.13/0.39  cnf(c_0_44, negated_conjecture, (r1_ordinal1(esk2_0,esk3_0)|r2_hidden(esk2_0,k2_tarski(esk3_0,esk3_0))|r2_hidden(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.13/0.39  fof(c_0_46, plain, ![X24, X25]:((~r1_ordinal1(X24,X25)|r1_tarski(X24,X25)|(~v3_ordinal1(X24)|~v3_ordinal1(X25)))&(~r1_tarski(X24,X25)|r1_ordinal1(X24,X25)|(~v3_ordinal1(X24)|~v3_ordinal1(X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.13/0.39  cnf(c_0_47, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k2_tarski(X2,X2))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.39  cnf(c_0_48, negated_conjecture, (r1_ordinal1(esk2_0,esk3_0)|r2_hidden(esk2_0,k2_tarski(esk3_0,esk3_0))), inference(sr,[status(thm)],[c_0_44, c_0_45])).
% 0.13/0.39  fof(c_0_49, plain, ![X16, X17]:(((r1_tarski(X16,X17)|~r2_xboole_0(X16,X17))&(X16!=X17|~r2_xboole_0(X16,X17)))&(~r1_tarski(X16,X17)|X16=X17|r2_xboole_0(X16,X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.13/0.39  cnf(c_0_50, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (r1_ordinal1(esk2_0,esk3_0)|r1_tarski(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.13/0.39  fof(c_0_52, plain, ![X31, X32]:(~r2_hidden(X31,X32)|~r1_tarski(X32,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.13/0.39  fof(c_0_53, plain, ![X27, X28]:(~v1_ordinal1(X27)|(~v3_ordinal1(X28)|(~r2_xboole_0(X27,X28)|r2_hidden(X27,X28)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).
% 0.13/0.39  cnf(c_0_54, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_26]), c_0_33])])).
% 0.13/0.39  cnf(c_0_56, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.39  cnf(c_0_57, plain, (r2_hidden(X1,X2)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.13/0.39  cnf(c_0_58, negated_conjecture, (esk3_0=esk2_0|r2_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.13/0.39  fof(c_0_59, plain, ![X22]:((v1_ordinal1(X22)|~v3_ordinal1(X22))&(v2_ordinal1(X22)|~v3_ordinal1(X22))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 0.13/0.39  fof(c_0_60, plain, ![X26]:r2_hidden(X26,k1_ordinal1(X26)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 0.13/0.39  cnf(c_0_61, negated_conjecture, (~r2_hidden(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_56, c_0_55])).
% 0.13/0.39  cnf(c_0_62, negated_conjecture, (esk3_0=esk2_0|~v1_ordinal1(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_26])]), c_0_45])).
% 0.13/0.39  cnf(c_0_63, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.13/0.39  cnf(c_0_64, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.13/0.39  cnf(c_0_65, negated_conjecture, (r1_ordinal1(esk2_0,esk3_0)), inference(sr,[status(thm)],[c_0_40, c_0_61])).
% 0.13/0.39  cnf(c_0_66, negated_conjecture, (esk3_0=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_33])])).
% 0.13/0.39  cnf(c_0_67, plain, (r2_hidden(X1,k2_xboole_0(X1,k2_tarski(X1,X1)))), inference(rw,[status(thm)],[c_0_64, c_0_23])).
% 0.13/0.39  cnf(c_0_68, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_65])]), c_0_66]), c_0_66]), c_0_66]), c_0_67])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 69
% 0.13/0.39  # Proof object clause steps            : 40
% 0.13/0.39  # Proof object formula steps           : 29
% 0.13/0.39  # Proof object conjectures             : 23
% 0.13/0.39  # Proof object clause conjectures      : 20
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 18
% 0.13/0.39  # Proof object initial formulas used   : 14
% 0.13/0.39  # Proof object generating inferences   : 14
% 0.13/0.39  # Proof object simplifying inferences  : 23
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 14
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 26
% 0.13/0.39  # Removed in clause preprocessing      : 2
% 0.13/0.39  # Initial clauses in saturation        : 24
% 0.13/0.39  # Processed clauses                    : 73
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 5
% 0.13/0.39  # ...remaining for further processing  : 67
% 0.13/0.39  # Other redundant clauses eliminated   : 1
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 2
% 0.13/0.39  # Backward-rewritten                   : 21
% 0.13/0.39  # Generated clauses                    : 161
% 0.13/0.39  # ...of the previous two non-trivial   : 156
% 0.13/0.39  # Contextual simplify-reflections      : 1
% 0.13/0.39  # Paramodulations                      : 138
% 0.13/0.39  # Factorizations                       : 16
% 0.13/0.39  # Equation resolutions                 : 5
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 41
% 0.13/0.39  #    Positive orientable unit clauses  : 4
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 3
% 0.13/0.39  #    Non-unit-clauses                  : 34
% 0.13/0.39  # Current number of unprocessed clauses: 106
% 0.13/0.39  # ...number of literals in the above   : 303
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 27
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 298
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 249
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 5
% 0.13/0.39  # Unit Clause-clause subsumption calls : 41
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 4
% 0.13/0.39  # BW rewrite match successes           : 3
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 3285
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.046 s
% 0.13/0.39  # System time              : 0.004 s
% 0.13/0.39  # Total time               : 0.050 s
% 0.13/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
