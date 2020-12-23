%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1957+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:09 EST 2020

% Result     : Theorem 9.33s
% Output     : CNFRefutation 9.33s
% Verified   : 
% Statistics : Number of formulae       :   19 (  25 expanded)
%              Number of clauses        :    8 (  10 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  27 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :    3 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_waybel_7,conjecture,(
    ! [X1] : u1_struct_0(k3_yellow_1(X1)) = k9_setfam_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_waybel_7)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT014+2.ax',redefinition_k9_setfam_1)).

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT026+2.ax',d2_yellow_1)).

fof(t4_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT026+2.ax',t4_yellow_1)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT026+2.ax',t1_yellow_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] : u1_struct_0(k3_yellow_1(X1)) = k9_setfam_1(X1) ),
    inference(assume_negation,[status(cth)],[t4_waybel_7])).

fof(c_0_6,negated_conjecture,(
    u1_struct_0(k3_yellow_1(esk1538_0)) != k9_setfam_1(esk1538_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_7,plain,(
    ! [X5107] : k9_setfam_1(X5107) = k1_zfmisc_1(X5107) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_8,plain,(
    ! [X9819] : k3_yellow_1(X9819) = k3_lattice3(k1_lattice3(X9819)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_9,plain,(
    ! [X9947] : k3_yellow_1(X9947) = k2_yellow_1(k9_setfam_1(X9947)) ),
    inference(variable_rename,[status(thm)],[t4_yellow_1])).

cnf(c_0_10,negated_conjecture,
    ( u1_struct_0(k3_yellow_1(esk1538_0)) != k9_setfam_1(esk1538_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X9926] :
      ( u1_struct_0(k2_yellow_1(X9926)) = X9926
      & u1_orders_2(k2_yellow_1(X9926)) = k1_yellow_1(X9926) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

cnf(c_0_15,negated_conjecture,
    ( u1_struct_0(k3_lattice3(k1_lattice3(esk1538_0))) != k1_zfmisc_1(esk1538_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11]),c_0_12])).

cnf(c_0_16,plain,
    ( k2_yellow_1(k1_zfmisc_1(X1)) = k3_lattice3(k1_lattice3(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_11]),c_0_12])).

cnf(c_0_17,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
