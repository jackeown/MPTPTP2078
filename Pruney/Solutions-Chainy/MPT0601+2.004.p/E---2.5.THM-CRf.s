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
% DateTime   : Thu Dec  3 10:52:13 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 107 expanded)
%              Number of clauses        :   35 (  51 expanded)
%              Number of leaves         :   11 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  171 ( 357 expanded)
%              Number of equality atoms :   33 (  85 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t205_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(fc2_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

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

fof(t150_relat_1,axiom,(
    ! [X1] : k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_11,plain,(
    ! [X46,X47,X48] :
      ( ( ~ r2_hidden(k4_tarski(X46,X47),X48)
        | r2_hidden(X47,k11_relat_1(X48,X46))
        | ~ v1_relat_1(X48) )
      & ( ~ r2_hidden(X47,k11_relat_1(X48,X46))
        | r2_hidden(k4_tarski(X46,X47),X48)
        | ~ v1_relat_1(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

fof(c_0_12,plain,(
    ! [X6] :
      ( X6 = k1_xboole_0
      | r2_hidden(esk1_1(X6),X6) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

fof(c_0_14,plain,(
    ! [X32,X33,X34,X36,X37,X38,X39,X41] :
      ( ( ~ r2_hidden(X34,X33)
        | r2_hidden(k4_tarski(X34,esk7_3(X32,X33,X34)),X32)
        | X33 != k1_relat_1(X32) )
      & ( ~ r2_hidden(k4_tarski(X36,X37),X32)
        | r2_hidden(X36,X33)
        | X33 != k1_relat_1(X32) )
      & ( ~ r2_hidden(esk8_2(X38,X39),X39)
        | ~ r2_hidden(k4_tarski(esk8_2(X38,X39),X41),X38)
        | X39 = k1_relat_1(X38) )
      & ( r2_hidden(esk8_2(X38,X39),X39)
        | r2_hidden(k4_tarski(esk8_2(X38,X39),esk9_2(X38,X39)),X38)
        | X39 = k1_relat_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_15,plain,(
    ! [X43,X44] :
      ( ~ v1_relat_1(X43)
      | v1_relat_1(k4_xboole_0(X43,X44)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).

fof(c_0_16,plain,(
    ! [X9,X10] : k4_xboole_0(X9,k2_xboole_0(X9,X10)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk11_0)
    & ( ~ r2_hidden(esk10_0,k1_relat_1(esk11_0))
      | k11_relat_1(esk11_0,esk10_0) = k1_xboole_0 )
    & ( r2_hidden(esk10_0,k1_relat_1(esk11_0))
      | k11_relat_1(esk11_0,esk10_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,esk7_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X13,X14,X15,X16,X18,X19,X20,X21,X23] :
      ( ( r2_hidden(k4_tarski(esk2_4(X13,X14,X15,X16),X16),X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k9_relat_1(X13,X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(esk2_4(X13,X14,X15,X16),X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k9_relat_1(X13,X14)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(X19,X18),X13)
        | ~ r2_hidden(X19,X14)
        | r2_hidden(X18,X15)
        | X15 != k9_relat_1(X13,X14)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(esk3_3(X13,X20,X21),X21)
        | ~ r2_hidden(k4_tarski(X23,esk3_3(X13,X20,X21)),X13)
        | ~ r2_hidden(X23,X20)
        | X21 = k9_relat_1(X13,X20)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk4_3(X13,X20,X21),esk3_3(X13,X20,X21)),X13)
        | r2_hidden(esk3_3(X13,X20,X21),X21)
        | X21 = k9_relat_1(X13,X20)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(esk4_3(X13,X20,X21),X20)
        | r2_hidden(esk3_3(X13,X20,X21),X21)
        | X21 = k9_relat_1(X13,X20)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).

cnf(c_0_22,plain,
    ( v1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( k11_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(X2,esk1_1(k11_relat_1(X1,X2))),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X1,esk7_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X45] : k9_relat_1(k1_xboole_0,X45) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t150_relat_1])).

cnf(c_0_30,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,negated_conjecture,
    ( k11_relat_1(esk11_0,esk10_0) = k1_xboole_0
    | ~ r2_hidden(esk10_0,k1_relat_1(esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( k11_relat_1(esk11_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X1,esk1_1(k11_relat_1(esk11_0,X1))),esk11_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(X1,k4_tarski(X2,esk7_3(k11_relat_1(X3,X1),k1_relat_1(k11_relat_1(X3,X1)),X2))),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X2,k1_relat_1(k11_relat_1(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_27])).

cnf(c_0_36,plain,
    ( r2_hidden(esk2_4(X1,X2,k9_relat_1(X1,X2),X3),X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(k4_tarski(esk10_0,X1),esk11_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_26])]),c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk10_0,k1_relat_1(esk11_0))
    | k11_relat_1(esk11_0,esk10_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( k11_relat_1(esk11_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(k11_relat_1(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_35])).

cnf(c_0_43,plain,
    ( r2_hidden(esk2_4(k1_xboole_0,X1,k1_xboole_0,X2),X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk7_3(esk11_0,k1_relat_1(esk11_0),esk10_0),k1_xboole_0)
    | ~ r2_hidden(esk10_0,k1_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_27])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk10_0,k1_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_46,plain,(
    ! [X25,X26,X27,X28,X29] :
      ( ( ~ r1_tarski(X25,X26)
        | ~ r2_hidden(k4_tarski(X27,X28),X25)
        | r2_hidden(k4_tarski(X27,X28),X26)
        | ~ v1_relat_1(X25) )
      & ( r2_hidden(k4_tarski(esk5_2(X25,X29),esk6_2(X25,X29)),X25)
        | r1_tarski(X25,X29)
        | ~ v1_relat_1(X25) )
      & ( ~ r2_hidden(k4_tarski(esk5_2(X25,X29),esk6_2(X25,X29)),X29)
        | r1_tarski(X25,X29)
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk7_3(esk11_0,k1_relat_1(esk11_0),esk10_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])])).

fof(c_0_49,plain,(
    ! [X11,X12] : ~ r2_hidden(X11,k2_zfmisc_1(X11,X12)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_50,plain,
    ( r2_hidden(k4_tarski(X3,X4),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_53,plain,
    ( r2_hidden(k4_tarski(X1,esk7_3(X2,k1_relat_1(X2),X1)),X3)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_27]),c_0_51])).

fof(c_0_54,plain,(
    ! [X8] : r1_tarski(k1_xboole_0,X8) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_55,plain,
    ( ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(k4_tarski(X2,esk7_3(X1,k1_relat_1(X1),X2)),X3)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_57,plain,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:18:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.028 s
% 0.12/0.39  # Presaturation interreduction done
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 0.12/0.39  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.12/0.39  fof(t205_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 0.12/0.39  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.12/0.39  fof(fc2_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k4_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 0.12/0.39  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.12/0.39  fof(d13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X5,X4),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 0.12/0.39  fof(t150_relat_1, axiom, ![X1]:k9_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 0.12/0.39  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 0.12/0.39  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.12/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.39  fof(c_0_11, plain, ![X46, X47, X48]:((~r2_hidden(k4_tarski(X46,X47),X48)|r2_hidden(X47,k11_relat_1(X48,X46))|~v1_relat_1(X48))&(~r2_hidden(X47,k11_relat_1(X48,X46))|r2_hidden(k4_tarski(X46,X47),X48)|~v1_relat_1(X48))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.12/0.39  fof(c_0_12, plain, ![X6]:(X6=k1_xboole_0|r2_hidden(esk1_1(X6),X6)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.12/0.39  fof(c_0_13, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t205_relat_1])).
% 0.12/0.39  fof(c_0_14, plain, ![X32, X33, X34, X36, X37, X38, X39, X41]:(((~r2_hidden(X34,X33)|r2_hidden(k4_tarski(X34,esk7_3(X32,X33,X34)),X32)|X33!=k1_relat_1(X32))&(~r2_hidden(k4_tarski(X36,X37),X32)|r2_hidden(X36,X33)|X33!=k1_relat_1(X32)))&((~r2_hidden(esk8_2(X38,X39),X39)|~r2_hidden(k4_tarski(esk8_2(X38,X39),X41),X38)|X39=k1_relat_1(X38))&(r2_hidden(esk8_2(X38,X39),X39)|r2_hidden(k4_tarski(esk8_2(X38,X39),esk9_2(X38,X39)),X38)|X39=k1_relat_1(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.12/0.39  fof(c_0_15, plain, ![X43, X44]:(~v1_relat_1(X43)|v1_relat_1(k4_xboole_0(X43,X44))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).
% 0.12/0.39  fof(c_0_16, plain, ![X9, X10]:k4_xboole_0(X9,k2_xboole_0(X9,X10))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.12/0.39  cnf(c_0_17, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.39  cnf(c_0_18, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.39  fof(c_0_19, negated_conjecture, (v1_relat_1(esk11_0)&((~r2_hidden(esk10_0,k1_relat_1(esk11_0))|k11_relat_1(esk11_0,esk10_0)=k1_xboole_0)&(r2_hidden(esk10_0,k1_relat_1(esk11_0))|k11_relat_1(esk11_0,esk10_0)!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.12/0.39  cnf(c_0_20, plain, (r2_hidden(k4_tarski(X1,esk7_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  fof(c_0_21, plain, ![X13, X14, X15, X16, X18, X19, X20, X21, X23]:((((r2_hidden(k4_tarski(esk2_4(X13,X14,X15,X16),X16),X13)|~r2_hidden(X16,X15)|X15!=k9_relat_1(X13,X14)|~v1_relat_1(X13))&(r2_hidden(esk2_4(X13,X14,X15,X16),X14)|~r2_hidden(X16,X15)|X15!=k9_relat_1(X13,X14)|~v1_relat_1(X13)))&(~r2_hidden(k4_tarski(X19,X18),X13)|~r2_hidden(X19,X14)|r2_hidden(X18,X15)|X15!=k9_relat_1(X13,X14)|~v1_relat_1(X13)))&((~r2_hidden(esk3_3(X13,X20,X21),X21)|(~r2_hidden(k4_tarski(X23,esk3_3(X13,X20,X21)),X13)|~r2_hidden(X23,X20))|X21=k9_relat_1(X13,X20)|~v1_relat_1(X13))&((r2_hidden(k4_tarski(esk4_3(X13,X20,X21),esk3_3(X13,X20,X21)),X13)|r2_hidden(esk3_3(X13,X20,X21),X21)|X21=k9_relat_1(X13,X20)|~v1_relat_1(X13))&(r2_hidden(esk4_3(X13,X20,X21),X20)|r2_hidden(esk3_3(X13,X20,X21),X21)|X21=k9_relat_1(X13,X20)|~v1_relat_1(X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).
% 0.12/0.39  cnf(c_0_22, plain, (v1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.39  cnf(c_0_23, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_24, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  cnf(c_0_25, plain, (k11_relat_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(X2,esk1_1(k11_relat_1(X1,X2))),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.12/0.39  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_27, plain, (r2_hidden(k4_tarski(X1,esk7_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_20])).
% 0.12/0.39  cnf(c_0_28, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.39  fof(c_0_29, plain, ![X45]:k9_relat_1(k1_xboole_0,X45)=k1_xboole_0, inference(variable_rename,[status(thm)],[t150_relat_1])).
% 0.12/0.39  cnf(c_0_30, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.12/0.39  cnf(c_0_31, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.39  cnf(c_0_32, negated_conjecture, (k11_relat_1(esk11_0,esk10_0)=k1_xboole_0|~r2_hidden(esk10_0,k1_relat_1(esk11_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_33, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_24])).
% 0.12/0.39  cnf(c_0_34, negated_conjecture, (k11_relat_1(esk11_0,X1)=k1_xboole_0|r2_hidden(k4_tarski(X1,esk1_1(k11_relat_1(esk11_0,X1))),esk11_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.39  cnf(c_0_35, plain, (r2_hidden(k4_tarski(X1,k4_tarski(X2,esk7_3(k11_relat_1(X3,X1),k1_relat_1(k11_relat_1(X3,X1)),X2))),X3)|~v1_relat_1(X3)|~r2_hidden(X2,k1_relat_1(k11_relat_1(X3,X1)))), inference(spm,[status(thm)],[c_0_17, c_0_27])).
% 0.12/0.39  cnf(c_0_36, plain, (r2_hidden(esk2_4(X1,X2,k9_relat_1(X1,X2),X3),X2)|~v1_relat_1(X1)|~r2_hidden(X3,k9_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_28])).
% 0.12/0.39  cnf(c_0_37, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.39  cnf(c_0_38, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_26])).
% 0.12/0.39  cnf(c_0_39, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~r2_hidden(k4_tarski(esk10_0,X1),esk11_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_26])]), c_0_33])).
% 0.12/0.39  cnf(c_0_40, negated_conjecture, (r2_hidden(esk10_0,k1_relat_1(esk11_0))|k11_relat_1(esk11_0,esk10_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_41, negated_conjecture, (k11_relat_1(esk11_0,X1)=k1_xboole_0|r2_hidden(X1,k1_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.39  cnf(c_0_42, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X3,k1_relat_1(k11_relat_1(X2,X1)))), inference(spm,[status(thm)],[c_0_33, c_0_35])).
% 0.12/0.39  cnf(c_0_43, plain, (r2_hidden(esk2_4(k1_xboole_0,X1,k1_xboole_0,X2),X1)|~r2_hidden(X2,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.12/0.39  cnf(c_0_44, negated_conjecture, (r2_hidden(esk7_3(esk11_0,k1_relat_1(esk11_0),esk10_0),k1_xboole_0)|~r2_hidden(esk10_0,k1_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_39, c_0_27])).
% 0.12/0.39  cnf(c_0_45, negated_conjecture, (r2_hidden(esk10_0,k1_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.12/0.39  fof(c_0_46, plain, ![X25, X26, X27, X28, X29]:((~r1_tarski(X25,X26)|(~r2_hidden(k4_tarski(X27,X28),X25)|r2_hidden(k4_tarski(X27,X28),X26))|~v1_relat_1(X25))&((r2_hidden(k4_tarski(esk5_2(X25,X29),esk6_2(X25,X29)),X25)|r1_tarski(X25,X29)|~v1_relat_1(X25))&(~r2_hidden(k4_tarski(esk5_2(X25,X29),esk6_2(X25,X29)),X29)|r1_tarski(X25,X29)|~v1_relat_1(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.12/0.39  cnf(c_0_47, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X3,k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.12/0.39  cnf(c_0_48, negated_conjecture, (r2_hidden(esk7_3(esk11_0,k1_relat_1(esk11_0),esk10_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45])])).
% 0.12/0.39  fof(c_0_49, plain, ![X11, X12]:~r2_hidden(X11,k2_zfmisc_1(X11,X12)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.12/0.39  cnf(c_0_50, plain, (r2_hidden(k4_tarski(X3,X4),X2)|~r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X3,X4),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.12/0.39  cnf(c_0_51, negated_conjecture, (r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.12/0.39  cnf(c_0_52, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.12/0.39  cnf(c_0_53, plain, (r2_hidden(k4_tarski(X1,esk7_3(X2,k1_relat_1(X2),X1)),X3)|~v1_relat_1(X2)|~r1_tarski(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_27]), c_0_51])).
% 0.12/0.39  fof(c_0_54, plain, ![X8]:r1_tarski(k1_xboole_0,X8), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.39  cnf(c_0_55, plain, (~v1_relat_1(X1)|~r1_tarski(X1,k2_zfmisc_1(k4_tarski(X2,esk7_3(X1,k1_relat_1(X1),X2)),X3))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.12/0.39  cnf(c_0_56, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.12/0.39  cnf(c_0_57, plain, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_38])]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 58
% 0.12/0.39  # Proof object clause steps            : 35
% 0.12/0.39  # Proof object formula steps           : 23
% 0.12/0.39  # Proof object conjectures             : 14
% 0.12/0.39  # Proof object clause conjectures      : 11
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 15
% 0.12/0.39  # Proof object initial formulas used   : 11
% 0.12/0.39  # Proof object generating inferences   : 16
% 0.12/0.39  # Proof object simplifying inferences  : 13
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 11
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 24
% 0.12/0.39  # Removed in clause preprocessing      : 0
% 0.12/0.39  # Initial clauses in saturation        : 24
% 0.12/0.39  # Processed clauses                    : 184
% 0.12/0.39  # ...of these trivial                  : 0
% 0.12/0.39  # ...subsumed                          : 61
% 0.12/0.39  # ...remaining for further processing  : 123
% 0.12/0.39  # Other redundant clauses eliminated   : 5
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 3
% 0.12/0.39  # Backward-rewritten                   : 18
% 0.12/0.39  # Generated clauses                    : 630
% 0.12/0.39  # ...of the previous two non-trivial   : 540
% 0.12/0.39  # Contextual simplify-reflections      : 3
% 0.12/0.39  # Paramodulations                      : 625
% 0.12/0.39  # Factorizations                       : 0
% 0.12/0.39  # Equation resolutions                 : 5
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 73
% 0.12/0.39  #    Positive orientable unit clauses  : 10
% 0.12/0.39  #    Positive unorientable unit clauses: 0
% 0.12/0.39  #    Negative unit clauses             : 1
% 0.12/0.39  #    Non-unit-clauses                  : 62
% 0.12/0.39  # Current number of unprocessed clauses: 368
% 0.12/0.39  # ...number of literals in the above   : 1289
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 45
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 392
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 342
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 67
% 0.12/0.39  # Unit Clause-clause subsumption calls : 6
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 21
% 0.12/0.39  # BW rewrite match successes           : 6
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 11090
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.040 s
% 0.12/0.39  # System time              : 0.006 s
% 0.12/0.39  # Total time               : 0.046 s
% 0.12/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
