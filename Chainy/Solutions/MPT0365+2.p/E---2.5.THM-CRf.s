%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0365+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:44 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   28 (  56 expanded)
%              Number of clauses        :   15 (  19 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :   89 ( 213 expanded)
%              Number of equality atoms :    9 (  33 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ( r1_xboole_0(X2,X3)
              & r1_xboole_0(k3_subset_1(X1,X2),k3_subset_1(X1,X3)) )
           => X2 = k3_subset_1(X1,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_subset_1)).

fof(t44_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,k3_subset_1(X1,X3))
          <=> r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t36_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(k3_subset_1(X1,X2),X3)
           => r1_tarski(k3_subset_1(X1,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

fof(t43_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,X3)
          <=> r1_tarski(X2,k3_subset_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( ( r1_xboole_0(X2,X3)
                & r1_xboole_0(k3_subset_1(X1,X2),k3_subset_1(X1,X3)) )
             => X2 = k3_subset_1(X1,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t46_subset_1])).

fof(c_0_7,plain,(
    ! [X1610,X1611,X1612] :
      ( ( ~ r1_xboole_0(X1611,k3_subset_1(X1610,X1612))
        | r1_tarski(X1611,X1612)
        | ~ m1_subset_1(X1612,k1_zfmisc_1(X1610))
        | ~ m1_subset_1(X1611,k1_zfmisc_1(X1610)) )
      & ( ~ r1_tarski(X1611,X1612)
        | r1_xboole_0(X1611,k3_subset_1(X1610,X1612))
        | ~ m1_subset_1(X1612,k1_zfmisc_1(X1610))
        | ~ m1_subset_1(X1611,k1_zfmisc_1(X1610)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_subset_1])])])])).

fof(c_0_8,negated_conjecture,
    ( m1_subset_1(esk69_0,k1_zfmisc_1(esk68_0))
    & m1_subset_1(esk70_0,k1_zfmisc_1(esk68_0))
    & r1_xboole_0(esk69_0,esk70_0)
    & r1_xboole_0(k3_subset_1(esk68_0,esk69_0),k3_subset_1(esk68_0,esk70_0))
    & esk69_0 != k3_subset_1(esk68_0,esk70_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_xboole_0(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk68_0,esk69_0),k3_subset_1(esk68_0,esk70_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk70_0,k1_zfmisc_1(esk68_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X1491,X1492] :
      ( ~ m1_subset_1(X1492,k1_zfmisc_1(X1491))
      | m1_subset_1(k3_subset_1(X1491,X1492),k1_zfmisc_1(X1491)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_13,plain,(
    ! [X1591,X1592,X1593] :
      ( ~ m1_subset_1(X1592,k1_zfmisc_1(X1591))
      | ~ m1_subset_1(X1593,k1_zfmisc_1(X1591))
      | ~ r1_tarski(k3_subset_1(X1591,X1592),X1593)
      | r1_tarski(k3_subset_1(X1591,X1593),X1592) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_subset_1])])])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk68_0,esk69_0),esk70_0)
    | ~ m1_subset_1(k3_subset_1(esk68_0,esk69_0),k1_zfmisc_1(esk68_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_15,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk69_0,k1_zfmisc_1(esk68_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_17,plain,(
    ! [X104,X105] :
      ( ( r1_tarski(X104,X105)
        | X104 != X105 )
      & ( r1_tarski(X105,X104)
        | X104 != X105 )
      & ( ~ r1_tarski(X104,X105)
        | ~ r1_tarski(X105,X104)
        | X104 = X105 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_18,plain,
    ( r1_tarski(k3_subset_1(X2,X3),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(k3_subset_1(X2,X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk68_0,esk69_0),esk70_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_20,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk68_0,esk70_0),esk69_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_11]),c_0_16])])).

cnf(c_0_22,negated_conjecture,
    ( esk69_0 != k3_subset_1(esk68_0,esk70_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_23,plain,(
    ! [X1607,X1608,X1609] :
      ( ( ~ r1_xboole_0(X1608,X1609)
        | r1_tarski(X1608,k3_subset_1(X1607,X1609))
        | ~ m1_subset_1(X1609,k1_zfmisc_1(X1607))
        | ~ m1_subset_1(X1608,k1_zfmisc_1(X1607)) )
      & ( ~ r1_tarski(X1608,k3_subset_1(X1607,X1609))
        | r1_xboole_0(X1608,X1609)
        | ~ m1_subset_1(X1609,k1_zfmisc_1(X1607))
        | ~ m1_subset_1(X1608,k1_zfmisc_1(X1607)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_subset_1])])])])).

cnf(c_0_24,negated_conjecture,
    ( ~ r1_tarski(esk69_0,k3_subset_1(esk68_0,esk70_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k3_subset_1(X3,X2))
    | ~ r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( r1_xboole_0(esk69_0,esk70_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_11]),c_0_16]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
