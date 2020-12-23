%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0468+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:46 EST 2020

% Result     : Theorem 0.87s
% Output     : CNFRefutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :   14 (  20 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   40 (  58 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t56_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),X1)
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(t135_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X1,X2))
        | r1_tarski(X1,k2_zfmisc_1(X2,X1)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t135_zfmisc_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),X1)
         => X1 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t56_relat_1])).

fof(c_0_4,plain,(
    ! [X2107,X2108,X2109,X2110,X2111] :
      ( ( ~ r1_tarski(X2107,X2108)
        | ~ r2_hidden(k4_tarski(X2109,X2110),X2107)
        | r2_hidden(k4_tarski(X2109,X2110),X2108)
        | ~ v1_relat_1(X2107) )
      & ( r2_hidden(k4_tarski(esk121_2(X2107,X2111),esk122_2(X2107,X2111)),X2107)
        | r1_tarski(X2107,X2111)
        | ~ v1_relat_1(X2107) )
      & ( ~ r2_hidden(k4_tarski(esk121_2(X2107,X2111),esk122_2(X2107,X2111)),X2111)
        | r1_tarski(X2107,X2111)
        | ~ v1_relat_1(X2107) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X2263,X2264] :
      ( v1_relat_1(esk138_0)
      & ~ r2_hidden(k4_tarski(X2263,X2264),esk138_0)
      & esk138_0 != k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])).

fof(c_0_6,plain,(
    ! [X1208,X1209] :
      ( ( ~ r1_tarski(X1208,k2_zfmisc_1(X1208,X1209))
        | X1208 = k1_xboole_0 )
      & ( ~ r1_tarski(X1208,k2_zfmisc_1(X1209,X1208))
        | X1208 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).

cnf(c_0_7,plain,
    ( r2_hidden(k4_tarski(esk121_2(X1,X2),esk122_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( v1_relat_1(esk138_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,X2),esk138_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(esk138_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( esk138_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),
    [proof]).
%------------------------------------------------------------------------------
