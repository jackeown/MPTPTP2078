%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:37 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   46 (  99 expanded)
%              Number of clauses        :   31 (  45 expanded)
%              Number of leaves         :    7 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  145 ( 406 expanded)
%              Number of equality atoms :   31 (  62 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   14 (   2 average)
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

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(c_0_7,plain,(
    ! [X5,X6,X8,X9,X10] :
      ( ( r2_hidden(esk1_2(X5,X6),X5)
        | r1_xboole_0(X5,X6) )
      & ( r2_hidden(esk1_2(X5,X6),X6)
        | r1_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | ~ r1_xboole_0(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_8,plain,(
    ! [X28,X29,X30,X32] :
      ( ( r2_hidden(esk6_3(X28,X29,X30),k2_relat_1(X30))
        | ~ r2_hidden(X28,k10_relat_1(X30,X29))
        | ~ v1_relat_1(X30) )
      & ( r2_hidden(k4_tarski(X28,esk6_3(X28,X29,X30)),X30)
        | ~ r2_hidden(X28,k10_relat_1(X30,X29))
        | ~ v1_relat_1(X30) )
      & ( r2_hidden(esk6_3(X28,X29,X30),X29)
        | ~ r2_hidden(X28,k10_relat_1(X30,X29))
        | ~ v1_relat_1(X30) )
      & ( ~ r2_hidden(X32,k2_relat_1(X30))
        | ~ r2_hidden(k4_tarski(X28,X32),X30)
        | ~ r2_hidden(X32,X29)
        | r2_hidden(X28,k10_relat_1(X30,X29))
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

fof(c_0_9,plain,(
    ! [X17,X18,X19,X21,X22,X23,X24,X26] :
      ( ( ~ r2_hidden(X19,X18)
        | r2_hidden(k4_tarski(esk3_3(X17,X18,X19),X19),X17)
        | X18 != k2_relat_1(X17) )
      & ( ~ r2_hidden(k4_tarski(X22,X21),X17)
        | r2_hidden(X21,X18)
        | X18 != k2_relat_1(X17) )
      & ( ~ r2_hidden(esk4_2(X23,X24),X24)
        | ~ r2_hidden(k4_tarski(X26,esk4_2(X23,X24)),X23)
        | X24 = k2_relat_1(X23) )
      & ( r2_hidden(esk4_2(X23,X24),X24)
        | r2_hidden(k4_tarski(esk5_2(X23,X24),esk4_2(X23,X24)),X23)
        | X24 = k2_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_10,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(esk6_3(X2,X3,X1),X4)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ r1_xboole_0(X4,X3) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,plain,(
    ! [X11] :
      ( X11 = k1_xboole_0
      | r2_hidden(esk2_1(X11),X11) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

fof(c_0_17,plain,(
    ! [X13,X14] :
      ( ( k2_zfmisc_1(X13,X14) != k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( X13 != k1_xboole_0
        | k2_zfmisc_1(X13,X14) = k1_xboole_0 )
      & ( X14 != k1_xboole_0
        | k2_zfmisc_1(X13,X14) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(esk3_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ r1_xboole_0(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_22,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & ( k10_relat_1(esk8_0,esk7_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk8_0),esk7_0) )
    & ( k10_relat_1(esk8_0,esk7_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk8_0),esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_24,plain,(
    ! [X15,X16] : ~ r2_hidden(X15,k2_zfmisc_1(X15,X16)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_25,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( k10_relat_1(esk8_0,esk7_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk8_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k10_relat_1(esk8_0,esk7_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk8_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_30])]),c_0_35])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(X1,k2_relat_1(esk8_0))
    | ~ r2_hidden(esk1_2(X1,k2_relat_1(esk8_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( k10_relat_1(esk8_0,esk7_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk8_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( r1_xboole_0(esk7_0,k2_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(esk8_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_34])])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.31  % Computer   : n025.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 13:08:50 EST 2020
% 0.16/0.31  % CPUTime    : 
% 0.16/0.31  # Version: 2.5pre002
% 0.16/0.31  # No SInE strategy applied
% 0.16/0.31  # Trying AutoSched0 for 299 seconds
% 0.16/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.16/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.16/0.40  #
% 0.16/0.40  # Preprocessing time       : 0.020 s
% 0.16/0.40  # Presaturation interreduction done
% 0.16/0.40  
% 0.16/0.40  # Proof found!
% 0.16/0.40  # SZS status Theorem
% 0.16/0.40  # SZS output start CNFRefutation
% 0.16/0.40  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.16/0.40  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 0.16/0.40  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.16/0.40  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.16/0.40  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 0.16/0.40  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.16/0.40  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.16/0.40  fof(c_0_7, plain, ![X5, X6, X8, X9, X10]:(((r2_hidden(esk1_2(X5,X6),X5)|r1_xboole_0(X5,X6))&(r2_hidden(esk1_2(X5,X6),X6)|r1_xboole_0(X5,X6)))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|~r1_xboole_0(X8,X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.16/0.40  fof(c_0_8, plain, ![X28, X29, X30, X32]:((((r2_hidden(esk6_3(X28,X29,X30),k2_relat_1(X30))|~r2_hidden(X28,k10_relat_1(X30,X29))|~v1_relat_1(X30))&(r2_hidden(k4_tarski(X28,esk6_3(X28,X29,X30)),X30)|~r2_hidden(X28,k10_relat_1(X30,X29))|~v1_relat_1(X30)))&(r2_hidden(esk6_3(X28,X29,X30),X29)|~r2_hidden(X28,k10_relat_1(X30,X29))|~v1_relat_1(X30)))&(~r2_hidden(X32,k2_relat_1(X30))|~r2_hidden(k4_tarski(X28,X32),X30)|~r2_hidden(X32,X29)|r2_hidden(X28,k10_relat_1(X30,X29))|~v1_relat_1(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.16/0.40  fof(c_0_9, plain, ![X17, X18, X19, X21, X22, X23, X24, X26]:(((~r2_hidden(X19,X18)|r2_hidden(k4_tarski(esk3_3(X17,X18,X19),X19),X17)|X18!=k2_relat_1(X17))&(~r2_hidden(k4_tarski(X22,X21),X17)|r2_hidden(X21,X18)|X18!=k2_relat_1(X17)))&((~r2_hidden(esk4_2(X23,X24),X24)|~r2_hidden(k4_tarski(X26,esk4_2(X23,X24)),X23)|X24=k2_relat_1(X23))&(r2_hidden(esk4_2(X23,X24),X24)|r2_hidden(k4_tarski(esk5_2(X23,X24),esk4_2(X23,X24)),X23)|X24=k2_relat_1(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.16/0.40  cnf(c_0_10, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.16/0.40  cnf(c_0_11, plain, (r2_hidden(esk6_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.16/0.40  cnf(c_0_12, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.40  cnf(c_0_13, plain, (~v1_relat_1(X1)|~r2_hidden(esk6_3(X2,X3,X1),X4)|~r2_hidden(X2,k10_relat_1(X1,X3))|~r1_xboole_0(X4,X3)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.16/0.40  cnf(c_0_14, plain, (r2_hidden(esk6_3(X1,X2,X3),k2_relat_1(X3))|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.16/0.40  fof(c_0_15, plain, ![X11]:(X11=k1_xboole_0|r2_hidden(esk2_1(X11),X11)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.16/0.40  fof(c_0_16, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.16/0.40  fof(c_0_17, plain, ![X13, X14]:((k2_zfmisc_1(X13,X14)!=k1_xboole_0|(X13=k1_xboole_0|X14=k1_xboole_0))&((X13!=k1_xboole_0|k2_zfmisc_1(X13,X14)=k1_xboole_0)&(X14!=k1_xboole_0|k2_zfmisc_1(X13,X14)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.16/0.40  cnf(c_0_18, plain, (r2_hidden(X3,k10_relat_1(X2,X4))|~r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.16/0.40  cnf(c_0_19, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_12])).
% 0.16/0.40  cnf(c_0_20, plain, (r2_hidden(k4_tarski(esk3_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.40  cnf(c_0_21, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,X3))|~r1_xboole_0(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.16/0.40  cnf(c_0_22, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.16/0.40  fof(c_0_23, negated_conjecture, (v1_relat_1(esk8_0)&((k10_relat_1(esk8_0,esk7_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk8_0),esk7_0))&(k10_relat_1(esk8_0,esk7_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk8_0),esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.16/0.40  fof(c_0_24, plain, ![X15, X16]:~r2_hidden(X15,k2_zfmisc_1(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.16/0.40  cnf(c_0_25, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.16/0.40  cnf(c_0_26, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_18, c_0_19])).
% 0.16/0.40  cnf(c_0_27, plain, (r2_hidden(k4_tarski(esk3_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_20])).
% 0.16/0.40  cnf(c_0_28, plain, (k10_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.16/0.40  cnf(c_0_29, negated_conjecture, (k10_relat_1(esk8_0,esk7_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk8_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.16/0.40  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.16/0.40  cnf(c_0_31, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.16/0.40  cnf(c_0_32, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_25])).
% 0.16/0.40  cnf(c_0_33, plain, (r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.16/0.40  cnf(c_0_34, negated_conjecture, (k10_relat_1(esk8_0,esk7_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.16/0.40  cnf(c_0_35, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.16/0.40  cnf(c_0_36, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.16/0.40  cnf(c_0_37, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk8_0))|~r2_hidden(X1,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_30])]), c_0_35])).
% 0.16/0.40  cnf(c_0_38, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.16/0.40  cnf(c_0_39, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_10, c_0_36])).
% 0.16/0.40  cnf(c_0_40, negated_conjecture, (r1_xboole_0(X1,k2_relat_1(esk8_0))|~r2_hidden(esk1_2(X1,k2_relat_1(esk8_0)),esk7_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.16/0.40  cnf(c_0_41, negated_conjecture, (k10_relat_1(esk8_0,esk7_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk8_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.16/0.40  cnf(c_0_42, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 0.16/0.40  cnf(c_0_43, negated_conjecture, (r1_xboole_0(esk7_0,k2_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_40, c_0_36])).
% 0.16/0.40  cnf(c_0_44, negated_conjecture, (~r1_xboole_0(k2_relat_1(esk8_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_34])])).
% 0.16/0.40  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), ['proof']).
% 0.16/0.40  # SZS output end CNFRefutation
% 0.16/0.40  # Proof object total steps             : 46
% 0.16/0.40  # Proof object clause steps            : 31
% 0.16/0.40  # Proof object formula steps           : 15
% 0.16/0.40  # Proof object conjectures             : 12
% 0.16/0.40  # Proof object clause conjectures      : 9
% 0.16/0.40  # Proof object formula conjectures     : 3
% 0.16/0.40  # Proof object initial clauses used    : 14
% 0.16/0.40  # Proof object initial formulas used   : 7
% 0.16/0.40  # Proof object generating inferences   : 12
% 0.16/0.40  # Proof object simplifying inferences  : 12
% 0.16/0.40  # Training examples: 0 positive, 0 negative
% 0.16/0.40  # Parsed axioms                        : 7
% 0.16/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.40  # Initial clauses                      : 19
% 0.16/0.40  # Removed in clause preprocessing      : 0
% 0.16/0.40  # Initial clauses in saturation        : 19
% 0.16/0.40  # Processed clauses                    : 1683
% 0.16/0.40  # ...of these trivial                  : 0
% 0.16/0.40  # ...subsumed                          : 1384
% 0.16/0.40  # ...remaining for further processing  : 299
% 0.16/0.40  # Other redundant clauses eliminated   : 4
% 0.16/0.40  # Clauses deleted for lack of memory   : 0
% 0.16/0.40  # Backward-subsumed                    : 0
% 0.16/0.40  # Backward-rewritten                   : 4
% 0.16/0.40  # Generated clauses                    : 4699
% 0.16/0.40  # ...of the previous two non-trivial   : 4265
% 0.16/0.40  # Contextual simplify-reflections      : 1
% 0.16/0.40  # Paramodulations                      : 4693
% 0.16/0.40  # Factorizations                       : 2
% 0.16/0.40  # Equation resolutions                 : 4
% 0.16/0.40  # Propositional unsat checks           : 0
% 0.16/0.40  #    Propositional check models        : 0
% 0.16/0.40  #    Propositional check unsatisfiable : 0
% 0.16/0.40  #    Propositional clauses             : 0
% 0.16/0.40  #    Propositional clauses after purity: 0
% 0.16/0.40  #    Propositional unsat core size     : 0
% 0.16/0.40  #    Propositional preprocessing time  : 0.000
% 0.16/0.40  #    Propositional encoding time       : 0.000
% 0.16/0.40  #    Propositional solver time         : 0.000
% 0.16/0.40  #    Success case prop preproc time    : 0.000
% 0.16/0.40  #    Success case prop encoding time   : 0.000
% 0.16/0.40  #    Success case prop solver time     : 0.000
% 0.16/0.40  # Current number of processed clauses  : 272
% 0.16/0.40  #    Positive orientable unit clauses  : 9
% 0.16/0.40  #    Positive unorientable unit clauses: 0
% 0.16/0.40  #    Negative unit clauses             : 4
% 0.16/0.40  #    Non-unit-clauses                  : 259
% 0.16/0.40  # Current number of unprocessed clauses: 2614
% 0.16/0.40  # ...number of literals in the above   : 9402
% 0.16/0.40  # Current number of archived formulas  : 0
% 0.16/0.40  # Current number of archived clauses   : 23
% 0.16/0.40  # Clause-clause subsumption calls (NU) : 14536
% 0.16/0.40  # Rec. Clause-clause subsumption calls : 10650
% 0.16/0.40  # Non-unit clause-clause subsumptions  : 728
% 0.16/0.40  # Unit Clause-clause subsumption calls : 5
% 0.16/0.40  # Rewrite failures with RHS unbound    : 0
% 0.16/0.40  # BW rewrite match attempts            : 2
% 0.16/0.40  # BW rewrite match successes           : 2
% 0.16/0.40  # Condensation attempts                : 0
% 0.16/0.40  # Condensation successes               : 0
% 0.16/0.40  # Termbank termtop insertions          : 78210
% 0.16/0.40  
% 0.16/0.40  # -------------------------------------------------
% 0.16/0.40  # User time                : 0.086 s
% 0.16/0.40  # System time              : 0.006 s
% 0.16/0.40  # Total time               : 0.092 s
% 0.16/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
