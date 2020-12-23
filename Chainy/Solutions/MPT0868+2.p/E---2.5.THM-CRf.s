%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0868+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:55 EST 2020

% Result     : Theorem 1.28s
% Output     : CNFRefutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 116 expanded)
%              Number of clauses        :   31 (  50 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :  123 ( 372 expanded)
%              Number of equality atoms :   68 ( 178 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t26_mcart_1,conjecture,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ! [X3] :
              ( m1_subset_1(X3,k2_zfmisc_1(X1,X2))
             => ( X3 != k1_mcart_1(X3)
                & X3 != k2_mcart_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_mcart_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',d2_subset_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',l13_xboole_0)).

fof(t20_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',fc6_relat_1)).

fof(fc1_zfmisc_1,axiom,(
    ! [X1,X2] : ~ v1_xboole_0(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',fc1_zfmisc_1)).

fof(t195_relat_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t195_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',fc1_xboole_0)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t60_relat_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & ~ ! [X3] :
                ( m1_subset_1(X3,k2_zfmisc_1(X1,X2))
               => ( X3 != k1_mcart_1(X3)
                  & X3 != k2_mcart_1(X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t26_mcart_1])).

fof(c_0_12,plain,(
    ! [X85,X86] :
      ( ( ~ m1_subset_1(X86,X85)
        | r2_hidden(X86,X85)
        | v1_xboole_0(X85) )
      & ( ~ r2_hidden(X86,X85)
        | m1_subset_1(X86,X85)
        | v1_xboole_0(X85) )
      & ( ~ m1_subset_1(X86,X85)
        | v1_xboole_0(X86)
        | ~ v1_xboole_0(X85) )
      & ( ~ v1_xboole_0(X86)
        | m1_subset_1(X86,X85)
        | ~ v1_xboole_0(X85) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_13,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & m1_subset_1(esk3_0,k2_zfmisc_1(esk1_0,esk2_0))
    & ( esk3_0 = k1_mcart_1(esk3_0)
      | esk3_0 = k2_mcart_1(esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_14,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk3_0,k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X412] :
      ( ~ v1_xboole_0(X412)
      | X412 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_18,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk1_0,esk2_0))
    | r2_hidden(esk3_0,k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_15])).

fof(c_0_20,plain,(
    ! [X63,X64,X65] :
      ( ( X63 != k1_mcart_1(X63)
        | X63 != k4_tarski(X64,X65) )
      & ( X63 != k2_mcart_1(X63)
        | X63 != k4_tarski(X64,X65) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).

fof(c_0_21,plain,(
    ! [X71,X72] :
      ( k1_mcart_1(k4_tarski(X71,X72)) = X71
      & k2_mcart_1(k4_tarski(X71,X72)) = X72 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

fof(c_0_22,plain,(
    ! [X66,X67] :
      ( ~ v1_relat_1(X67)
      | ~ r2_hidden(X66,X67)
      | X66 = k4_tarski(k1_mcart_1(X66),k2_mcart_1(X66)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | r2_hidden(esk3_0,k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_25,plain,(
    ! [X389,X390] : v1_relat_1(k2_zfmisc_1(X389,X390)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_26,plain,
    ( X1 != k1_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(esk3_0,k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( X1 != k2_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k4_tarski(X1,X2) != X1 ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_26]),c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk3_0),k2_mcart_1(esk3_0)) = esk3_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_35,negated_conjecture,
    ( esk3_0 = k1_mcart_1(esk3_0)
    | esk3_0 = k2_mcart_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,plain,
    ( k4_tarski(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_31]),c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k1_mcart_1(esk3_0) != esk3_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | r2_hidden(esk3_0,k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_39,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])).

fof(c_0_40,plain,(
    ! [X600,X601] : ~ v1_xboole_0(k4_tarski(X600,X601)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_zfmisc_1])])).

cnf(c_0_41,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | r2_hidden(k1_xboole_0,k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_42,plain,(
    ! [X397,X398] :
      ( ( k1_relat_1(k2_zfmisc_1(X397,X398)) = X397
        | X397 = k1_xboole_0
        | X398 = k1_xboole_0 )
      & ( k2_relat_1(k2_zfmisc_1(X397,X398)) = X398
        | X397 = k1_xboole_0
        | X398 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).

cnf(c_0_43,plain,
    ( ~ v1_xboole_0(k4_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_xboole_0),k2_mcart_1(k1_xboole_0)) = k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_41]),c_0_30])])).

cnf(c_0_45,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_46,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_48,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_49,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_50,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])]),c_0_49]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
