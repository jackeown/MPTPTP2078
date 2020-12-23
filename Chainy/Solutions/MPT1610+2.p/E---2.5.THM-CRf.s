%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1610+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:06 EST 2020

% Result     : Theorem 6.15s
% Output     : CNFRefutation 6.15s
% Verified   : 
% Statistics : Number of formulae       :   33 (  36 expanded)
%              Number of clauses        :   16 (  17 expanded)
%              Number of leaves         :    8 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   59 (  62 expanded)
%              Number of equality atoms :   27 (  30 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_yellow_1,conjecture,(
    ! [X1] : k3_yellow_0(k3_yellow_1(X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',d1_zfmisc_1)).

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(t4_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT014+2.ax',redefinition_k9_setfam_1)).

fof(t13_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k1_xboole_0,X1)
       => k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t7_boole)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t2_xboole_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] : k3_yellow_0(k3_yellow_1(X1)) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t18_yellow_1])).

fof(c_0_9,plain,(
    ! [X990,X991,X992,X993,X994,X995] :
      ( ( ~ r2_hidden(X992,X991)
        | r1_tarski(X992,X990)
        | X991 != k1_zfmisc_1(X990) )
      & ( ~ r1_tarski(X993,X990)
        | r2_hidden(X993,X991)
        | X991 != k1_zfmisc_1(X990) )
      & ( ~ r2_hidden(esk21_2(X994,X995),X995)
        | ~ r1_tarski(esk21_2(X994,X995),X994)
        | X995 = k1_zfmisc_1(X994) )
      & ( r2_hidden(esk21_2(X994,X995),X995)
        | r1_tarski(esk21_2(X994,X995),X994)
        | X995 = k1_zfmisc_1(X994) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_10,negated_conjecture,(
    k3_yellow_0(k3_yellow_1(esk1124_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X9811] : k3_yellow_1(X9811) = k3_lattice3(k1_lattice3(X9811)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_12,plain,(
    ! [X9856] : k3_yellow_1(X9856) = k2_yellow_1(k9_setfam_1(X9856)) ),
    inference(variable_rename,[status(thm)],[t4_yellow_1])).

fof(c_0_13,plain,(
    ! [X5107] : k9_setfam_1(X5107) = k1_zfmisc_1(X5107) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_14,plain,(
    ! [X9841] :
      ( v1_xboole_0(X9841)
      | ~ r2_hidden(k1_xboole_0,X9841)
      | k3_yellow_0(k2_yellow_1(X9841)) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t13_yellow_1])])])).

fof(c_0_15,plain,(
    ! [X389,X390] :
      ( ~ r2_hidden(X389,X390)
      | ~ v1_xboole_0(X390) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_17,plain,(
    ! [X247] : r1_tarski(k1_xboole_0,X247) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_18,negated_conjecture,
    ( k3_yellow_0(k3_yellow_1(esk1124_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( v1_xboole_0(X1)
    | k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( k3_yellow_0(k3_lattice3(k1_lattice3(esk1124_0))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( k2_yellow_1(k1_zfmisc_1(X1)) = k3_lattice3(k1_lattice3(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_19])).

cnf(c_0_28,plain,
    ( k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(csr,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( k3_yellow_0(k2_yellow_1(k1_zfmisc_1(esk1124_0))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( k3_yellow_0(k2_yellow_1(k1_zfmisc_1(X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
