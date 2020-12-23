%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0326+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:43 EST 2020

% Result     : Theorem 1.36s
% Output     : CNFRefutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   29 (  51 expanded)
%              Number of clauses        :   16 (  20 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 ( 147 expanded)
%              Number of equality atoms :   24 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t139_zfmisc_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2,X3,X4] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
            | r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X4,X3)) )
         => r1_tarski(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(t138_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t69_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t65_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t2_xboole_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2,X3,X4] :
            ( ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
              | r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X4,X3)) )
           => r1_tarski(X2,X4) ) ) ),
    inference(assume_negation,[status(cth)],[t139_zfmisc_1])).

fof(c_0_7,plain,(
    ! [X1212,X1213,X1214,X1215] :
      ( ( r1_tarski(X1212,X1214)
        | k2_zfmisc_1(X1212,X1213) = k1_xboole_0
        | ~ r1_tarski(k2_zfmisc_1(X1212,X1213),k2_zfmisc_1(X1214,X1215)) )
      & ( r1_tarski(X1213,X1215)
        | k2_zfmisc_1(X1212,X1213) = k1_xboole_0
        | ~ r1_tarski(k2_zfmisc_1(X1212,X1213),k2_zfmisc_1(X1214,X1215)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_zfmisc_1])])])).

fof(c_0_8,negated_conjecture,
    ( ~ v1_xboole_0(esk51_0)
    & ( r1_tarski(k2_zfmisc_1(esk51_0,esk52_0),k2_zfmisc_1(esk53_0,esk54_0))
      | r1_tarski(k2_zfmisc_1(esk52_0,esk51_0),k2_zfmisc_1(esk54_0,esk53_0)) )
    & ~ r1_tarski(esk52_0,esk54_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,X2)
    | k2_zfmisc_1(X1,X3) = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk51_0,esk52_0),k2_zfmisc_1(esk53_0,esk54_0))
    | r1_tarski(k2_zfmisc_1(esk52_0,esk51_0),k2_zfmisc_1(esk54_0,esk53_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( ~ r1_tarski(esk52_0,esk54_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X347,X348] :
      ( v1_xboole_0(X348)
      | ~ r1_tarski(X348,X347)
      | ~ r1_xboole_0(X348,X347) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

fof(c_0_13,plain,(
    ! [X339] : r1_xboole_0(X339,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_14,plain,(
    ! [X1130,X1131] :
      ( ( k2_zfmisc_1(X1130,X1131) != k1_xboole_0
        | X1130 = k1_xboole_0
        | X1131 = k1_xboole_0 )
      & ( X1130 != k1_xboole_0
        | k2_zfmisc_1(X1130,X1131) = k1_xboole_0 )
      & ( X1131 != k1_xboole_0
        | k2_zfmisc_1(X1130,X1131) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | k2_zfmisc_1(X3,X1) = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( k2_zfmisc_1(esk52_0,esk51_0) = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(esk51_0,esk52_0),k2_zfmisc_1(esk53_0,esk54_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])).

cnf(c_0_17,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( k2_zfmisc_1(esk52_0,esk51_0) = k1_xboole_0
    | k2_zfmisc_1(esk51_0,esk52_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_11])).

fof(c_0_21,plain,(
    ! [X239] : r1_tarski(k1_xboole_0,X239) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_xboole_0(esk51_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( esk52_0 = k1_xboole_0
    | esk51_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_19])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_tarski(esk51_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( esk51_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_24]),c_0_25])])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
