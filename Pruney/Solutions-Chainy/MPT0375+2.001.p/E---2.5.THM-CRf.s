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
% DateTime   : Thu Dec  3 10:46:52 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 112 expanded)
%              Number of clauses        :   35 (  52 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  175 ( 389 expanded)
%              Number of equality atoms :   33 (  88 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t57_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ! [X3] :
          ( m1_subset_1(X3,X1)
         => ! [X4] :
              ( m1_subset_1(X4,X1)
             => ( X1 != k1_xboole_0
               => m1_subset_1(k1_enumset1(X2,X3,X4),k1_zfmisc_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_subset_1)).

fof(t55_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ( X1 != k1_xboole_0
       => m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(t37_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,X1)
       => ! [X3] :
            ( m1_subset_1(X3,X1)
           => ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( X1 != k1_xboole_0
                 => m1_subset_1(k1_enumset1(X2,X3,X4),k1_zfmisc_1(X1)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_subset_1])).

fof(c_0_12,plain,(
    ! [X46,X47] :
      ( ~ m1_subset_1(X47,X46)
      | X46 = k1_xboole_0
      | m1_subset_1(k1_tarski(X47),k1_zfmisc_1(X46)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_subset_1])])).

fof(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,esk3_0)
    & m1_subset_1(esk5_0,esk3_0)
    & m1_subset_1(esk6_0,esk3_0)
    & esk3_0 != k1_xboole_0
    & ~ m1_subset_1(k1_enumset1(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_14,plain,(
    ! [X12,X13,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X14,X13)
        | X14 = X12
        | X13 != k1_tarski(X12) )
      & ( X15 != X12
        | r2_hidden(X15,X13)
        | X13 != k1_tarski(X12) )
      & ( ~ r2_hidden(esk1_2(X16,X17),X17)
        | esk1_2(X16,X17) != X16
        | X17 = k1_tarski(X16) )
      & ( r2_hidden(esk1_2(X16,X17),X17)
        | esk1_2(X16,X17) = X16
        | X17 = k1_tarski(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_15,plain,(
    ! [X28,X29,X30,X31,X32,X33] :
      ( ( ~ r2_hidden(X30,X29)
        | r1_tarski(X30,X28)
        | X29 != k1_zfmisc_1(X28) )
      & ( ~ r1_tarski(X31,X28)
        | r2_hidden(X31,X29)
        | X29 != k1_zfmisc_1(X28) )
      & ( ~ r2_hidden(esk2_2(X32,X33),X33)
        | ~ r1_tarski(esk2_2(X32,X33),X32)
        | X33 = k1_zfmisc_1(X32) )
      & ( r2_hidden(esk2_2(X32,X33),X33)
        | r1_tarski(esk2_2(X32,X33),X32)
        | X33 = k1_zfmisc_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_16,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X9,X8)
      | r1_tarski(k2_xboole_0(X7,X9),X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

fof(c_0_17,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(X43))
      | ~ r2_hidden(X45,X44)
      | r2_hidden(X45,X43) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_18,plain,
    ( X2 = k1_xboole_0
    | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk6_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
    ! [X37,X38,X39] :
      ( ( r2_hidden(X37,X39)
        | ~ r1_tarski(k2_tarski(X37,X38),X39) )
      & ( r2_hidden(X38,X39)
        | ~ r1_tarski(k2_tarski(X37,X38),X39) )
      & ( ~ r2_hidden(X37,X39)
        | ~ r2_hidden(X38,X39)
        | r1_tarski(k2_tarski(X37,X38),X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_25,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk6_0),k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_tarski(X1) ),
    inference(er,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X19,X20,X21] : k1_enumset1(X19,X20,X21) = k2_xboole_0(k1_tarski(X19),k2_tarski(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_29,plain,(
    ! [X40,X41] :
      ( ( ~ m1_subset_1(X41,X40)
        | r2_hidden(X41,X40)
        | v1_xboole_0(X40) )
      & ( ~ r2_hidden(X41,X40)
        | m1_subset_1(X41,X40)
        | v1_xboole_0(X40) )
      & ( ~ m1_subset_1(X41,X40)
        | v1_xboole_0(X41)
        | ~ v1_xboole_0(X40) )
      & ( ~ v1_xboole_0(X41)
        | m1_subset_1(X41,X40)
        | ~ v1_xboole_0(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_30,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | ~ v1_xboole_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_31,plain,
    ( r2_hidden(k2_xboole_0(X1,X2),X3)
    | X3 != k1_zfmisc_1(X4)
    | ~ r1_tarski(X2,X4)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_33,plain,(
    ! [X35,X36] :
      ( ( ~ r1_tarski(k1_tarski(X35),X36)
        | r2_hidden(X35,X36) )
      & ( ~ r2_hidden(X35,X36)
        | r1_tarski(k1_tarski(X35),X36) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_zfmisc_1])])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,k1_tarski(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( ~ m1_subset_1(k1_enumset1(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( r2_hidden(k2_xboole_0(X1,k2_tarski(X2,X3)),X4)
    | X4 != k1_zfmisc_1(X5)
    | ~ r1_tarski(X1,X5)
    | ~ r2_hidden(X3,X5)
    | ~ r2_hidden(X2,X5) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_34]),c_0_20])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk6_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(k1_tarski(esk4_0),k2_tarski(esk5_0,esk6_0)),k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,plain,
    ( r2_hidden(k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)),X4)
    | X4 != k1_zfmisc_1(X5)
    | ~ r2_hidden(X3,X5)
    | ~ r2_hidden(X2,X5)
    | ~ r2_hidden(X1,X5) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,k1_tarski(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | r2_hidden(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(k2_xboole_0(k1_tarski(esk4_0),k2_tarski(esk5_0,esk6_0)),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k2_xboole_0(k1_tarski(X1),k2_tarski(X2,esk6_0)),X3)
    | X3 != k1_zfmisc_1(esk3_0)
    | ~ r2_hidden(X2,esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_36])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 17:19:00 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  # Version: 2.5pre002
% 0.20/0.33  # No SInE strategy applied
% 0.20/0.33  # Trying AutoSched0 for 299 seconds
% 2.14/2.32  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 2.14/2.32  # and selection function PSelectComplexExceptUniqMaxHorn.
% 2.14/2.32  #
% 2.14/2.32  # Preprocessing time       : 0.030 s
% 2.14/2.32  
% 2.14/2.32  # Proof found!
% 2.14/2.32  # SZS status Theorem
% 2.14/2.32  # SZS output start CNFRefutation
% 2.14/2.32  fof(t57_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m1_subset_1(X4,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k1_enumset1(X2,X3,X4),k1_zfmisc_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_subset_1)).
% 2.14/2.32  fof(t55_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 2.14/2.32  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.14/2.32  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.14/2.32  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.14/2.32  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.14/2.32  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.14/2.32  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.14/2.32  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.14/2.32  fof(t7_boole, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 2.14/2.32  fof(t37_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 2.14/2.32  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m1_subset_1(X4,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k1_enumset1(X2,X3,X4),k1_zfmisc_1(X1))))))), inference(assume_negation,[status(cth)],[t57_subset_1])).
% 2.14/2.32  fof(c_0_12, plain, ![X46, X47]:(~m1_subset_1(X47,X46)|(X46=k1_xboole_0|m1_subset_1(k1_tarski(X47),k1_zfmisc_1(X46)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_subset_1])])).
% 2.14/2.32  fof(c_0_13, negated_conjecture, (m1_subset_1(esk4_0,esk3_0)&(m1_subset_1(esk5_0,esk3_0)&(m1_subset_1(esk6_0,esk3_0)&(esk3_0!=k1_xboole_0&~m1_subset_1(k1_enumset1(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 2.14/2.32  fof(c_0_14, plain, ![X12, X13, X14, X15, X16, X17]:(((~r2_hidden(X14,X13)|X14=X12|X13!=k1_tarski(X12))&(X15!=X12|r2_hidden(X15,X13)|X13!=k1_tarski(X12)))&((~r2_hidden(esk1_2(X16,X17),X17)|esk1_2(X16,X17)!=X16|X17=k1_tarski(X16))&(r2_hidden(esk1_2(X16,X17),X17)|esk1_2(X16,X17)=X16|X17=k1_tarski(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 2.14/2.32  fof(c_0_15, plain, ![X28, X29, X30, X31, X32, X33]:(((~r2_hidden(X30,X29)|r1_tarski(X30,X28)|X29!=k1_zfmisc_1(X28))&(~r1_tarski(X31,X28)|r2_hidden(X31,X29)|X29!=k1_zfmisc_1(X28)))&((~r2_hidden(esk2_2(X32,X33),X33)|~r1_tarski(esk2_2(X32,X33),X32)|X33=k1_zfmisc_1(X32))&(r2_hidden(esk2_2(X32,X33),X33)|r1_tarski(esk2_2(X32,X33),X32)|X33=k1_zfmisc_1(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 2.14/2.32  fof(c_0_16, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X9,X8)|r1_tarski(k2_xboole_0(X7,X9),X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 2.14/2.32  fof(c_0_17, plain, ![X43, X44, X45]:(~m1_subset_1(X44,k1_zfmisc_1(X43))|(~r2_hidden(X45,X44)|r2_hidden(X45,X43))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 2.14/2.32  cnf(c_0_18, plain, (X2=k1_xboole_0|m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.14/2.32  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk6_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.14/2.32  cnf(c_0_20, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.14/2.32  cnf(c_0_21, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.14/2.32  cnf(c_0_22, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.14/2.32  cnf(c_0_23, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.14/2.32  fof(c_0_24, plain, ![X37, X38, X39]:(((r2_hidden(X37,X39)|~r1_tarski(k2_tarski(X37,X38),X39))&(r2_hidden(X38,X39)|~r1_tarski(k2_tarski(X37,X38),X39)))&(~r2_hidden(X37,X39)|~r2_hidden(X38,X39)|r1_tarski(k2_tarski(X37,X38),X39))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 2.14/2.32  cnf(c_0_25, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.14/2.32  cnf(c_0_26, negated_conjecture, (m1_subset_1(k1_tarski(esk6_0),k1_zfmisc_1(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 2.14/2.32  cnf(c_0_27, plain, (r2_hidden(X1,X2)|X2!=k1_tarski(X1)), inference(er,[status(thm)],[c_0_21])).
% 2.14/2.32  fof(c_0_28, plain, ![X19, X20, X21]:k1_enumset1(X19,X20,X21)=k2_xboole_0(k1_tarski(X19),k2_tarski(X20,X21)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 2.14/2.32  fof(c_0_29, plain, ![X40, X41]:(((~m1_subset_1(X41,X40)|r2_hidden(X41,X40)|v1_xboole_0(X40))&(~r2_hidden(X41,X40)|m1_subset_1(X41,X40)|v1_xboole_0(X40)))&((~m1_subset_1(X41,X40)|v1_xboole_0(X41)|~v1_xboole_0(X40))&(~v1_xboole_0(X41)|m1_subset_1(X41,X40)|~v1_xboole_0(X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 2.14/2.32  fof(c_0_30, plain, ![X5, X6]:(~r2_hidden(X5,X6)|~v1_xboole_0(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).
% 2.14/2.32  cnf(c_0_31, plain, (r2_hidden(k2_xboole_0(X1,X2),X3)|X3!=k1_zfmisc_1(X4)|~r1_tarski(X2,X4)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 2.14/2.32  cnf(c_0_32, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.14/2.32  fof(c_0_33, plain, ![X35, X36]:((~r1_tarski(k1_tarski(X35),X36)|r2_hidden(X35,X36))&(~r2_hidden(X35,X36)|r1_tarski(k1_tarski(X35),X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_zfmisc_1])])).
% 2.14/2.32  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.14/2.32  cnf(c_0_35, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,k1_tarski(esk6_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 2.14/2.32  cnf(c_0_36, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[c_0_27])).
% 2.14/2.32  cnf(c_0_37, negated_conjecture, (~m1_subset_1(k1_enumset1(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.14/2.32  cnf(c_0_38, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.14/2.32  cnf(c_0_39, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.14/2.32  cnf(c_0_40, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.14/2.32  cnf(c_0_41, plain, (r2_hidden(k2_xboole_0(X1,k2_tarski(X2,X3)),X4)|X4!=k1_zfmisc_1(X5)|~r1_tarski(X1,X5)|~r2_hidden(X3,X5)|~r2_hidden(X2,X5)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 2.14/2.32  cnf(c_0_42, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.14/2.32  cnf(c_0_43, negated_conjecture, (m1_subset_1(k1_tarski(esk5_0),k1_zfmisc_1(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_34]), c_0_20])).
% 2.14/2.32  cnf(c_0_44, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.14/2.32  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.14/2.32  cnf(c_0_46, negated_conjecture, (r2_hidden(esk6_0,esk3_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 2.14/2.32  cnf(c_0_47, negated_conjecture, (~m1_subset_1(k2_xboole_0(k1_tarski(esk4_0),k2_tarski(esk5_0,esk6_0)),k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 2.14/2.32  cnf(c_0_48, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_39, c_0_40])).
% 2.14/2.32  cnf(c_0_49, plain, (r2_hidden(k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)),X4)|X4!=k1_zfmisc_1(X5)|~r2_hidden(X3,X5)|~r2_hidden(X2,X5)|~r2_hidden(X1,X5)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 2.14/2.32  cnf(c_0_50, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,k1_tarski(esk5_0))), inference(spm,[status(thm)],[c_0_25, c_0_43])).
% 2.14/2.32  cnf(c_0_51, negated_conjecture, (v1_xboole_0(esk3_0)|r2_hidden(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 2.14/2.32  cnf(c_0_52, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_40, c_0_46])).
% 2.14/2.32  cnf(c_0_53, negated_conjecture, (~r2_hidden(k2_xboole_0(k1_tarski(esk4_0),k2_tarski(esk5_0,esk6_0)),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 2.14/2.32  cnf(c_0_54, negated_conjecture, (r2_hidden(k2_xboole_0(k1_tarski(X1),k2_tarski(X2,esk6_0)),X3)|X3!=k1_zfmisc_1(esk3_0)|~r2_hidden(X2,esk3_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_49, c_0_46])).
% 2.14/2.32  cnf(c_0_55, negated_conjecture, (r2_hidden(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_50, c_0_36])).
% 2.14/2.32  cnf(c_0_56, negated_conjecture, (r2_hidden(esk4_0,esk3_0)), inference(sr,[status(thm)],[c_0_51, c_0_52])).
% 2.14/2.32  cnf(c_0_57, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_56])]), ['proof']).
% 2.14/2.32  # SZS output end CNFRefutation
% 2.14/2.32  # Proof object total steps             : 58
% 2.14/2.32  # Proof object clause steps            : 35
% 2.14/2.32  # Proof object formula steps           : 23
% 2.14/2.32  # Proof object conjectures             : 21
% 2.14/2.32  # Proof object clause conjectures      : 18
% 2.14/2.32  # Proof object formula conjectures     : 3
% 2.14/2.32  # Proof object initial clauses used    : 16
% 2.14/2.32  # Proof object initial formulas used   : 11
% 2.14/2.32  # Proof object generating inferences   : 15
% 2.14/2.32  # Proof object simplifying inferences  : 9
% 2.14/2.32  # Training examples: 0 positive, 0 negative
% 2.14/2.32  # Parsed axioms                        : 15
% 2.14/2.32  # Removed by relevancy pruning/SinE    : 0
% 2.14/2.32  # Initial clauses                      : 31
% 2.14/2.32  # Removed in clause preprocessing      : 1
% 2.14/2.32  # Initial clauses in saturation        : 30
% 2.14/2.32  # Processed clauses                    : 7697
% 2.14/2.32  # ...of these trivial                  : 8
% 2.14/2.32  # ...subsumed                          : 4669
% 2.14/2.32  # ...remaining for further processing  : 3020
% 2.14/2.32  # Other redundant clauses eliminated   : 10
% 2.14/2.32  # Clauses deleted for lack of memory   : 0
% 2.14/2.32  # Backward-subsumed                    : 13
% 2.14/2.32  # Backward-rewritten                   : 2
% 2.14/2.32  # Generated clauses                    : 154439
% 2.14/2.32  # ...of the previous two non-trivial   : 154246
% 2.14/2.32  # Contextual simplify-reflections      : 7
% 2.14/2.32  # Paramodulations                      : 153937
% 2.14/2.32  # Factorizations                       : 35
% 2.14/2.32  # Equation resolutions                 : 466
% 2.14/2.32  # Propositional unsat checks           : 0
% 2.14/2.32  #    Propositional check models        : 0
% 2.14/2.32  #    Propositional check unsatisfiable : 0
% 2.14/2.32  #    Propositional clauses             : 0
% 2.14/2.32  #    Propositional clauses after purity: 0
% 2.14/2.32  #    Propositional unsat core size     : 0
% 2.14/2.32  #    Propositional preprocessing time  : 0.000
% 2.14/2.32  #    Propositional encoding time       : 0.000
% 2.14/2.32  #    Propositional solver time         : 0.000
% 2.14/2.32  #    Success case prop preproc time    : 0.000
% 2.14/2.32  #    Success case prop encoding time   : 0.000
% 2.14/2.32  #    Success case prop solver time     : 0.000
% 2.14/2.32  # Current number of processed clauses  : 3003
% 2.14/2.32  #    Positive orientable unit clauses  : 30
% 2.14/2.32  #    Positive unorientable unit clauses: 4
% 2.14/2.32  #    Negative unit clauses             : 9
% 2.14/2.32  #    Non-unit-clauses                  : 2960
% 2.14/2.32  # Current number of unprocessed clauses: 146126
% 2.14/2.32  # ...number of literals in the above   : 795515
% 2.14/2.32  # Current number of archived formulas  : 0
% 2.14/2.32  # Current number of archived clauses   : 17
% 2.14/2.32  # Clause-clause subsumption calls (NU) : 1765364
% 2.14/2.32  # Rec. Clause-clause subsumption calls : 846794
% 2.14/2.32  # Non-unit clause-clause subsumptions  : 4110
% 2.14/2.32  # Unit Clause-clause subsumption calls : 1076
% 2.14/2.32  # Rewrite failures with RHS unbound    : 0
% 2.14/2.32  # BW rewrite match attempts            : 145
% 2.14/2.32  # BW rewrite match successes           : 21
% 2.14/2.32  # Condensation attempts                : 0
% 2.14/2.32  # Condensation successes               : 0
% 2.14/2.32  # Termbank termtop insertions          : 2932205
% 2.14/2.33  
% 2.14/2.33  # -------------------------------------------------
% 2.14/2.33  # User time                : 1.922 s
% 2.14/2.33  # System time              : 0.078 s
% 2.14/2.33  # Total time               : 2.000 s
% 2.14/2.33  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
