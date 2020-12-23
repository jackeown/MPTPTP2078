%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:11 EST 2020

% Result     : Theorem 1.11s
% Output     : CNFRefutation 1.11s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 309 expanded)
%              Number of clauses        :   43 ( 145 expanded)
%              Number of leaves         :    7 (  78 expanded)
%              Depth                    :   15
%              Number of atoms          :  159 ( 672 expanded)
%              Number of equality atoms :   96 ( 476 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( X3 = k1_tarski(k4_tarski(X1,X2))
       => ( k1_relat_1(X3) = k1_tarski(X1)
          & k2_relat_1(X3) = k1_tarski(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t35_zfmisc_1,axiom,(
    ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(t34_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))
    <=> ( X1 = X3
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( X3 = k1_tarski(k4_tarski(X1,X2))
         => ( k1_relat_1(X3) = k1_tarski(X1)
            & k2_relat_1(X3) = k1_tarski(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_relat_1])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk17_0)
    & esk17_0 = k1_tarski(k4_tarski(esk15_0,esk16_0))
    & ( k1_relat_1(esk17_0) != k1_tarski(esk15_0)
      | k2_relat_1(esk17_0) != k1_tarski(esk16_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_9,plain,(
    ! [X35] : k2_tarski(X35,X35) = k1_tarski(X35) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_10,plain,(
    ! [X57,X58] : k2_zfmisc_1(k1_tarski(X57),k1_tarski(X58)) = k1_tarski(k4_tarski(X57,X58)) ),
    inference(variable_rename,[status(thm)],[t35_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X53,X54,X55,X56] :
      ( ( X53 = X55
        | ~ r2_hidden(k4_tarski(X53,X54),k2_zfmisc_1(k1_tarski(X55),k1_tarski(X56))) )
      & ( X54 = X56
        | ~ r2_hidden(k4_tarski(X53,X54),k2_zfmisc_1(k1_tarski(X55),k1_tarski(X56))) )
      & ( X53 != X55
        | X54 != X56
        | r2_hidden(k4_tarski(X53,X54),k2_zfmisc_1(k1_tarski(X55),k1_tarski(X56))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_zfmisc_1])])])).

cnf(c_0_12,negated_conjecture,
    ( esk17_0 = k1_tarski(k4_tarski(esk15_0,esk16_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(k1_tarski(X4),k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( esk17_0 = k2_tarski(k4_tarski(esk15_0,esk16_0),k4_tarski(esk15_0,esk16_0)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X2)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_13]),c_0_13]),c_0_13])).

cnf(c_0_18,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(k2_tarski(X4,X4),k2_tarski(X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_13]),c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( k2_zfmisc_1(k2_tarski(esk15_0,esk15_0),k2_tarski(esk16_0,esk16_0)) = esk17_0 ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_20,plain,(
    ! [X94,X95,X96,X98,X99,X100,X101,X103] :
      ( ( ~ r2_hidden(X96,X95)
        | r2_hidden(k4_tarski(esk10_3(X94,X95,X96),X96),X94)
        | X95 != k2_relat_1(X94) )
      & ( ~ r2_hidden(k4_tarski(X99,X98),X94)
        | r2_hidden(X98,X95)
        | X95 != k2_relat_1(X94) )
      & ( ~ r2_hidden(esk11_2(X100,X101),X101)
        | ~ r2_hidden(k4_tarski(X103,esk11_2(X100,X101)),X100)
        | X101 = k2_relat_1(X100) )
      & ( r2_hidden(esk11_2(X100,X101),X101)
        | r2_hidden(k4_tarski(esk12_2(X100,X101),esk11_2(X100,X101)),X100)
        | X101 = k2_relat_1(X100) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_21,negated_conjecture,
    ( X1 = esk16_0
    | ~ r2_hidden(k4_tarski(X2,X1),esk17_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(esk10_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X23,X24,X25,X26,X27,X28] :
      ( ( ~ r2_hidden(X25,X24)
        | X25 = X23
        | X24 != k1_tarski(X23) )
      & ( X26 != X23
        | r2_hidden(X26,X24)
        | X24 != k1_tarski(X23) )
      & ( ~ r2_hidden(esk4_2(X27,X28),X28)
        | esk4_2(X27,X28) != X27
        | X28 = k1_tarski(X27) )
      & ( r2_hidden(esk4_2(X27,X28),X28)
        | esk4_2(X27,X28) = X27
        | X28 = k1_tarski(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X4)))
    | X1 != X2
    | X3 != X4 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( X1 = esk16_0
    | X2 != k2_relat_1(esk17_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | esk4_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_tarski(X2,X2),k2_tarski(X4,X4)))
    | X3 != X4
    | X1 != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_13]),c_0_13])).

cnf(c_0_29,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_tarski(X2,X2),k2_tarski(X4,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_13]),c_0_13])).

fof(c_0_30,plain,(
    ! [X83,X84,X85,X87,X88,X89,X90,X92] :
      ( ( ~ r2_hidden(X85,X84)
        | r2_hidden(k4_tarski(X85,esk7_3(X83,X84,X85)),X83)
        | X84 != k1_relat_1(X83) )
      & ( ~ r2_hidden(k4_tarski(X87,X88),X83)
        | r2_hidden(X87,X84)
        | X84 != k1_relat_1(X83) )
      & ( ~ r2_hidden(esk8_2(X89,X90),X90)
        | ~ r2_hidden(k4_tarski(esk8_2(X89,X90),X92),X89)
        | X90 = k1_relat_1(X89) )
      & ( r2_hidden(esk8_2(X89,X90),X90)
        | r2_hidden(k4_tarski(esk8_2(X89,X90),esk9_2(X89,X90)),X89)
        | X90 = k1_relat_1(X89) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_31,negated_conjecture,
    ( X1 = esk16_0
    | ~ r2_hidden(X1,k2_relat_1(esk17_0)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( X2 = k2_tarski(X1,X1)
    | esk4_2(X1,X2) = X1
    | r2_hidden(esk4_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_13])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X2))) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).

cnf(c_0_34,negated_conjecture,
    ( X1 = esk15_0
    | ~ r2_hidden(k4_tarski(X1,X2),esk17_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_19])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(X1,esk7_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( esk4_2(X1,k2_relat_1(esk17_0)) = esk16_0
    | esk4_2(X1,k2_relat_1(esk17_0)) = X1
    | k2_relat_1(esk17_0) = k2_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(esk15_0,esk16_0),esk17_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_19])).

cnf(c_0_39,negated_conjecture,
    ( X1 = esk15_0
    | X2 != k1_relat_1(esk17_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk4_2(X1,X2),X2)
    | esk4_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( esk4_2(X1,k2_relat_1(esk17_0)) = esk16_0
    | k2_relat_1(esk17_0) = k2_tarski(X1,X1)
    | X1 != esk16_0 ),
    inference(ef,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk16_0,X1)
    | X1 != k2_relat_1(esk17_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( X1 = esk15_0
    | ~ r2_hidden(X1,k1_relat_1(esk17_0)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(esk17_0) != k1_tarski(esk15_0)
    | k2_relat_1(esk17_0) != k1_tarski(esk16_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_45,plain,
    ( X2 = k2_tarski(X1,X1)
    | esk4_2(X1,X2) != X1
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_40,c_0_13])).

cnf(c_0_46,negated_conjecture,
    ( k2_relat_1(esk17_0) = k2_tarski(esk16_0,esk16_0)
    | esk4_2(esk16_0,k2_relat_1(esk17_0)) = esk16_0 ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk16_0,k2_relat_1(esk17_0)) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( esk4_2(X1,k1_relat_1(esk17_0)) = esk15_0
    | esk4_2(X1,k1_relat_1(esk17_0)) = X1
    | k1_relat_1(esk17_0) = k2_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_32])).

cnf(c_0_49,negated_conjecture,
    ( k1_relat_1(esk17_0) != k2_tarski(esk15_0,esk15_0)
    | k2_relat_1(esk17_0) != k2_tarski(esk16_0,esk16_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_13]),c_0_13])).

cnf(c_0_50,negated_conjecture,
    ( k2_relat_1(esk17_0) = k2_tarski(esk16_0,esk16_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_52,negated_conjecture,
    ( esk4_2(X1,k1_relat_1(esk17_0)) = esk15_0
    | k1_relat_1(esk17_0) = k2_tarski(X1,X1)
    | X1 != esk15_0 ),
    inference(ef,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( k1_relat_1(esk17_0) != k2_tarski(esk15_0,esk15_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk15_0,X1)
    | X1 != k1_relat_1(esk17_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_38])).

cnf(c_0_55,negated_conjecture,
    ( esk4_2(esk15_0,k1_relat_1(esk17_0)) = esk15_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_52]),c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk15_0,k1_relat_1(esk17_0)) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_55]),c_0_56])]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:59:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 1.11/1.31  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 1.11/1.31  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.11/1.31  #
% 1.11/1.31  # Preprocessing time       : 0.031 s
% 1.11/1.31  # Presaturation interreduction done
% 1.11/1.31  
% 1.11/1.31  # Proof found!
% 1.11/1.31  # SZS status Theorem
% 1.11/1.31  # SZS output start CNFRefutation
% 1.11/1.31  fof(t23_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(X3=k1_tarski(k4_tarski(X1,X2))=>(k1_relat_1(X3)=k1_tarski(X1)&k2_relat_1(X3)=k1_tarski(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relat_1)).
% 1.11/1.31  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.11/1.31  fof(t35_zfmisc_1, axiom, ![X1, X2]:k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 1.11/1.31  fof(t34_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))<=>(X1=X3&X2=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 1.11/1.31  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 1.11/1.31  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.11/1.31  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 1.11/1.31  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(X3=k1_tarski(k4_tarski(X1,X2))=>(k1_relat_1(X3)=k1_tarski(X1)&k2_relat_1(X3)=k1_tarski(X2))))), inference(assume_negation,[status(cth)],[t23_relat_1])).
% 1.11/1.31  fof(c_0_8, negated_conjecture, (v1_relat_1(esk17_0)&(esk17_0=k1_tarski(k4_tarski(esk15_0,esk16_0))&(k1_relat_1(esk17_0)!=k1_tarski(esk15_0)|k2_relat_1(esk17_0)!=k1_tarski(esk16_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 1.11/1.31  fof(c_0_9, plain, ![X35]:k2_tarski(X35,X35)=k1_tarski(X35), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.11/1.31  fof(c_0_10, plain, ![X57, X58]:k2_zfmisc_1(k1_tarski(X57),k1_tarski(X58))=k1_tarski(k4_tarski(X57,X58)), inference(variable_rename,[status(thm)],[t35_zfmisc_1])).
% 1.11/1.31  fof(c_0_11, plain, ![X53, X54, X55, X56]:(((X53=X55|~r2_hidden(k4_tarski(X53,X54),k2_zfmisc_1(k1_tarski(X55),k1_tarski(X56))))&(X54=X56|~r2_hidden(k4_tarski(X53,X54),k2_zfmisc_1(k1_tarski(X55),k1_tarski(X56)))))&(X53!=X55|X54!=X56|r2_hidden(k4_tarski(X53,X54),k2_zfmisc_1(k1_tarski(X55),k1_tarski(X56))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_zfmisc_1])])])).
% 1.11/1.31  cnf(c_0_12, negated_conjecture, (esk17_0=k1_tarski(k4_tarski(esk15_0,esk16_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.11/1.31  cnf(c_0_13, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.11/1.31  cnf(c_0_14, plain, (k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.11/1.31  cnf(c_0_15, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(k1_tarski(X4),k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.11/1.31  cnf(c_0_16, negated_conjecture, (esk17_0=k2_tarski(k4_tarski(esk15_0,esk16_0),k4_tarski(esk15_0,esk16_0))), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 1.11/1.31  cnf(c_0_17, plain, (k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X2))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_13]), c_0_13]), c_0_13])).
% 1.11/1.31  cnf(c_0_18, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(k2_tarski(X4,X4),k2_tarski(X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_13]), c_0_13])).
% 1.11/1.31  cnf(c_0_19, negated_conjecture, (k2_zfmisc_1(k2_tarski(esk15_0,esk15_0),k2_tarski(esk16_0,esk16_0))=esk17_0), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 1.11/1.31  fof(c_0_20, plain, ![X94, X95, X96, X98, X99, X100, X101, X103]:(((~r2_hidden(X96,X95)|r2_hidden(k4_tarski(esk10_3(X94,X95,X96),X96),X94)|X95!=k2_relat_1(X94))&(~r2_hidden(k4_tarski(X99,X98),X94)|r2_hidden(X98,X95)|X95!=k2_relat_1(X94)))&((~r2_hidden(esk11_2(X100,X101),X101)|~r2_hidden(k4_tarski(X103,esk11_2(X100,X101)),X100)|X101=k2_relat_1(X100))&(r2_hidden(esk11_2(X100,X101),X101)|r2_hidden(k4_tarski(esk12_2(X100,X101),esk11_2(X100,X101)),X100)|X101=k2_relat_1(X100)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 1.11/1.31  cnf(c_0_21, negated_conjecture, (X1=esk16_0|~r2_hidden(k4_tarski(X2,X1),esk17_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 1.11/1.31  cnf(c_0_22, plain, (r2_hidden(k4_tarski(esk10_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.11/1.31  fof(c_0_23, plain, ![X23, X24, X25, X26, X27, X28]:(((~r2_hidden(X25,X24)|X25=X23|X24!=k1_tarski(X23))&(X26!=X23|r2_hidden(X26,X24)|X24!=k1_tarski(X23)))&((~r2_hidden(esk4_2(X27,X28),X28)|esk4_2(X27,X28)!=X27|X28=k1_tarski(X27))&(r2_hidden(esk4_2(X27,X28),X28)|esk4_2(X27,X28)=X27|X28=k1_tarski(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 1.11/1.31  cnf(c_0_24, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X4)))|X1!=X2|X3!=X4), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.11/1.31  cnf(c_0_25, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X4)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.11/1.31  cnf(c_0_26, negated_conjecture, (X1=esk16_0|X2!=k2_relat_1(esk17_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 1.11/1.31  cnf(c_0_27, plain, (r2_hidden(esk4_2(X1,X2),X2)|esk4_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.11/1.31  cnf(c_0_28, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_tarski(X2,X2),k2_tarski(X4,X4)))|X3!=X4|X1!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_13]), c_0_13])).
% 1.11/1.31  cnf(c_0_29, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_tarski(X2,X2),k2_tarski(X4,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_13]), c_0_13])).
% 1.11/1.31  fof(c_0_30, plain, ![X83, X84, X85, X87, X88, X89, X90, X92]:(((~r2_hidden(X85,X84)|r2_hidden(k4_tarski(X85,esk7_3(X83,X84,X85)),X83)|X84!=k1_relat_1(X83))&(~r2_hidden(k4_tarski(X87,X88),X83)|r2_hidden(X87,X84)|X84!=k1_relat_1(X83)))&((~r2_hidden(esk8_2(X89,X90),X90)|~r2_hidden(k4_tarski(esk8_2(X89,X90),X92),X89)|X90=k1_relat_1(X89))&(r2_hidden(esk8_2(X89,X90),X90)|r2_hidden(k4_tarski(esk8_2(X89,X90),esk9_2(X89,X90)),X89)|X90=k1_relat_1(X89)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 1.11/1.31  cnf(c_0_31, negated_conjecture, (X1=esk16_0|~r2_hidden(X1,k2_relat_1(esk17_0))), inference(er,[status(thm)],[c_0_26])).
% 1.11/1.31  cnf(c_0_32, plain, (X2=k2_tarski(X1,X1)|esk4_2(X1,X2)=X1|r2_hidden(esk4_2(X1,X2),X2)), inference(rw,[status(thm)],[c_0_27, c_0_13])).
% 1.11/1.31  cnf(c_0_33, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X2)))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).
% 1.11/1.31  cnf(c_0_34, negated_conjecture, (X1=esk15_0|~r2_hidden(k4_tarski(X1,X2),esk17_0)), inference(spm,[status(thm)],[c_0_29, c_0_19])).
% 1.11/1.31  cnf(c_0_35, plain, (r2_hidden(k4_tarski(X1,esk7_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.11/1.31  cnf(c_0_36, negated_conjecture, (esk4_2(X1,k2_relat_1(esk17_0))=esk16_0|esk4_2(X1,k2_relat_1(esk17_0))=X1|k2_relat_1(esk17_0)=k2_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 1.11/1.31  cnf(c_0_37, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.11/1.31  cnf(c_0_38, negated_conjecture, (r2_hidden(k4_tarski(esk15_0,esk16_0),esk17_0)), inference(spm,[status(thm)],[c_0_33, c_0_19])).
% 1.11/1.31  cnf(c_0_39, negated_conjecture, (X1=esk15_0|X2!=k1_relat_1(esk17_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 1.11/1.31  cnf(c_0_40, plain, (X2=k1_tarski(X1)|~r2_hidden(esk4_2(X1,X2),X2)|esk4_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.11/1.31  cnf(c_0_41, negated_conjecture, (esk4_2(X1,k2_relat_1(esk17_0))=esk16_0|k2_relat_1(esk17_0)=k2_tarski(X1,X1)|X1!=esk16_0), inference(ef,[status(thm)],[c_0_36])).
% 1.11/1.31  cnf(c_0_42, negated_conjecture, (r2_hidden(esk16_0,X1)|X1!=k2_relat_1(esk17_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.11/1.31  cnf(c_0_43, negated_conjecture, (X1=esk15_0|~r2_hidden(X1,k1_relat_1(esk17_0))), inference(er,[status(thm)],[c_0_39])).
% 1.11/1.31  cnf(c_0_44, negated_conjecture, (k1_relat_1(esk17_0)!=k1_tarski(esk15_0)|k2_relat_1(esk17_0)!=k1_tarski(esk16_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.11/1.31  cnf(c_0_45, plain, (X2=k2_tarski(X1,X1)|esk4_2(X1,X2)!=X1|~r2_hidden(esk4_2(X1,X2),X2)), inference(rw,[status(thm)],[c_0_40, c_0_13])).
% 1.11/1.31  cnf(c_0_46, negated_conjecture, (k2_relat_1(esk17_0)=k2_tarski(esk16_0,esk16_0)|esk4_2(esk16_0,k2_relat_1(esk17_0))=esk16_0), inference(er,[status(thm)],[c_0_41])).
% 1.11/1.31  cnf(c_0_47, negated_conjecture, (r2_hidden(esk16_0,k2_relat_1(esk17_0))), inference(er,[status(thm)],[c_0_42])).
% 1.11/1.31  cnf(c_0_48, negated_conjecture, (esk4_2(X1,k1_relat_1(esk17_0))=esk15_0|esk4_2(X1,k1_relat_1(esk17_0))=X1|k1_relat_1(esk17_0)=k2_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_43, c_0_32])).
% 1.11/1.31  cnf(c_0_49, negated_conjecture, (k1_relat_1(esk17_0)!=k2_tarski(esk15_0,esk15_0)|k2_relat_1(esk17_0)!=k2_tarski(esk16_0,esk16_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_13]), c_0_13])).
% 1.11/1.31  cnf(c_0_50, negated_conjecture, (k2_relat_1(esk17_0)=k2_tarski(esk16_0,esk16_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 1.11/1.31  cnf(c_0_51, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.11/1.31  cnf(c_0_52, negated_conjecture, (esk4_2(X1,k1_relat_1(esk17_0))=esk15_0|k1_relat_1(esk17_0)=k2_tarski(X1,X1)|X1!=esk15_0), inference(ef,[status(thm)],[c_0_48])).
% 1.11/1.31  cnf(c_0_53, negated_conjecture, (k1_relat_1(esk17_0)!=k2_tarski(esk15_0,esk15_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50])])).
% 1.11/1.31  cnf(c_0_54, negated_conjecture, (r2_hidden(esk15_0,X1)|X1!=k1_relat_1(esk17_0)), inference(spm,[status(thm)],[c_0_51, c_0_38])).
% 1.11/1.31  cnf(c_0_55, negated_conjecture, (esk4_2(esk15_0,k1_relat_1(esk17_0))=esk15_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_52]), c_0_53])).
% 1.11/1.31  cnf(c_0_56, negated_conjecture, (r2_hidden(esk15_0,k1_relat_1(esk17_0))), inference(er,[status(thm)],[c_0_54])).
% 1.11/1.31  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_55]), c_0_56])]), c_0_53]), ['proof']).
% 1.11/1.31  # SZS output end CNFRefutation
% 1.11/1.31  # Proof object total steps             : 58
% 1.11/1.31  # Proof object clause steps            : 43
% 1.11/1.31  # Proof object formula steps           : 15
% 1.11/1.31  # Proof object conjectures             : 28
% 1.11/1.31  # Proof object clause conjectures      : 25
% 1.11/1.31  # Proof object formula conjectures     : 3
% 1.11/1.31  # Proof object initial clauses used    : 13
% 1.11/1.31  # Proof object initial formulas used   : 7
% 1.11/1.31  # Proof object generating inferences   : 19
% 1.11/1.31  # Proof object simplifying inferences  : 25
% 1.11/1.31  # Training examples: 0 positive, 0 negative
% 1.11/1.31  # Parsed axioms                        : 36
% 1.11/1.31  # Removed by relevancy pruning/SinE    : 0
% 1.11/1.31  # Initial clauses                      : 80
% 1.11/1.31  # Removed in clause preprocessing      : 2
% 1.11/1.31  # Initial clauses in saturation        : 78
% 1.11/1.31  # Processed clauses                    : 5271
% 1.11/1.31  # ...of these trivial                  : 124
% 1.11/1.31  # ...subsumed                          : 3759
% 1.11/1.31  # ...remaining for further processing  : 1388
% 1.11/1.31  # Other redundant clauses eliminated   : 603
% 1.11/1.31  # Clauses deleted for lack of memory   : 0
% 1.11/1.31  # Backward-subsumed                    : 61
% 1.11/1.31  # Backward-rewritten                   : 95
% 1.11/1.31  # Generated clauses                    : 61628
% 1.11/1.31  # ...of the previous two non-trivial   : 58460
% 1.11/1.31  # Contextual simplify-reflections      : 22
% 1.11/1.31  # Paramodulations                      : 60665
% 1.11/1.31  # Factorizations                       : 68
% 1.11/1.31  # Equation resolutions                 : 835
% 1.11/1.31  # Propositional unsat checks           : 0
% 1.11/1.31  #    Propositional check models        : 0
% 1.11/1.31  #    Propositional check unsatisfiable : 0
% 1.11/1.31  #    Propositional clauses             : 0
% 1.11/1.31  #    Propositional clauses after purity: 0
% 1.11/1.31  #    Propositional unsat core size     : 0
% 1.11/1.31  #    Propositional preprocessing time  : 0.000
% 1.11/1.31  #    Propositional encoding time       : 0.000
% 1.11/1.31  #    Propositional solver time         : 0.000
% 1.11/1.31  #    Success case prop preproc time    : 0.000
% 1.11/1.31  #    Success case prop encoding time   : 0.000
% 1.11/1.31  #    Success case prop solver time     : 0.000
% 1.11/1.31  # Current number of processed clauses  : 1127
% 1.11/1.31  #    Positive orientable unit clauses  : 142
% 1.11/1.31  #    Positive unorientable unit clauses: 6
% 1.11/1.31  #    Negative unit clauses             : 54
% 1.11/1.31  #    Non-unit-clauses                  : 925
% 1.11/1.31  # Current number of unprocessed clauses: 53178
% 1.11/1.31  # ...number of literals in the above   : 266751
% 1.11/1.31  # Current number of archived formulas  : 0
% 1.11/1.31  # Current number of archived clauses   : 234
% 1.11/1.31  # Clause-clause subsumption calls (NU) : 123395
% 1.11/1.31  # Rec. Clause-clause subsumption calls : 74716
% 1.11/1.31  # Non-unit clause-clause subsumptions  : 2281
% 1.11/1.31  # Unit Clause-clause subsumption calls : 13395
% 1.11/1.31  # Rewrite failures with RHS unbound    : 0
% 1.11/1.31  # BW rewrite match attempts            : 114
% 1.11/1.31  # BW rewrite match successes           : 80
% 1.11/1.31  # Condensation attempts                : 0
% 1.11/1.31  # Condensation successes               : 0
% 1.11/1.31  # Termbank termtop insertions          : 1011910
% 1.11/1.31  
% 1.11/1.31  # -------------------------------------------------
% 1.11/1.31  # User time                : 0.923 s
% 1.11/1.31  # System time              : 0.031 s
% 1.11/1.31  # Total time               : 0.954 s
% 1.11/1.31  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
