%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0291+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:41 EST 2020

% Result     : Theorem 35.67s
% Output     : CNFRefutation 35.67s
% Verified   : 
% Statistics : Number of formulae       :   26 (  38 expanded)
%              Number of clauses        :   17 (  18 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :   10
%              Number of atoms          :   87 ( 152 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_xboole_0(X3,X2) )
     => r1_xboole_0(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_zfmisc_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',symmetry_r1_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',t3_xboole_0)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ! [X3] :
            ( r2_hidden(X3,X1)
           => r1_xboole_0(X3,X2) )
       => r1_xboole_0(k3_tarski(X1),X2) ) ),
    inference(assume_negation,[status(cth)],[t98_zfmisc_1])).

fof(c_0_5,plain,(
    ! [X72,X73] :
      ( ~ r1_xboole_0(X72,X73)
      | r1_xboole_0(X73,X72) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_6,negated_conjecture,(
    ! [X1247] :
      ( ( ~ r2_hidden(X1247,esk33_0)
        | r1_xboole_0(X1247,esk34_0) )
      & ~ r1_xboole_0(k3_tarski(esk33_0),esk34_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_7,plain,(
    ! [X84,X85,X87,X88,X89] :
      ( ( r2_hidden(esk10_2(X84,X85),X84)
        | r1_xboole_0(X84,X85) )
      & ( r2_hidden(esk10_2(X84,X85),X85)
        | r1_xboole_0(X84,X85) )
      & ( ~ r2_hidden(X89,X87)
        | ~ r2_hidden(X89,X88)
        | ~ r1_xboole_0(X87,X88) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_8,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r1_xboole_0(X1,esk34_0)
    | ~ r2_hidden(X1,esk33_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r1_xboole_0(esk34_0,X1)
    | ~ r2_hidden(X1,esk33_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

fof(c_0_12,plain,(
    ! [X1005,X1006,X1007,X1009,X1010,X1011,X1012,X1014] :
      ( ( r2_hidden(X1007,esk27_3(X1005,X1006,X1007))
        | ~ r2_hidden(X1007,X1006)
        | X1006 != k3_tarski(X1005) )
      & ( r2_hidden(esk27_3(X1005,X1006,X1007),X1005)
        | ~ r2_hidden(X1007,X1006)
        | X1006 != k3_tarski(X1005) )
      & ( ~ r2_hidden(X1009,X1010)
        | ~ r2_hidden(X1010,X1005)
        | r2_hidden(X1009,X1006)
        | X1006 != k3_tarski(X1005) )
      & ( ~ r2_hidden(esk28_2(X1011,X1012),X1012)
        | ~ r2_hidden(esk28_2(X1011,X1012),X1014)
        | ~ r2_hidden(X1014,X1011)
        | X1012 = k3_tarski(X1011) )
      & ( r2_hidden(esk28_2(X1011,X1012),esk29_2(X1011,X1012))
        | r2_hidden(esk28_2(X1011,X1012),X1012)
        | X1012 = k3_tarski(X1011) )
      & ( r2_hidden(esk29_2(X1011,X1012),X1011)
        | r2_hidden(esk28_2(X1011,X1012),X1012)
        | X1012 = k3_tarski(X1011) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_13,negated_conjecture,
    ( ~ r2_hidden(X1,esk34_0)
    | ~ r2_hidden(X2,esk33_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,plain,
    ( r2_hidden(esk10_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,esk27_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r1_xboole_0(esk34_0,X1)
    | ~ r2_hidden(esk10_2(esk34_0,X1),X2)
    | ~ r2_hidden(X2,esk33_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,esk27_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_18,plain,
    ( r2_hidden(esk27_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( r1_xboole_0(esk34_0,X1)
    | ~ r2_hidden(esk27_3(X2,k3_tarski(X2),esk10_2(esk34_0,X1)),esk33_0)
    | ~ r2_hidden(esk10_2(esk34_0,X1),k3_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,plain,
    ( r2_hidden(esk27_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( r1_xboole_0(esk34_0,X1)
    | ~ r2_hidden(esk10_2(esk34_0,X1),k3_tarski(esk33_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_22,plain,
    ( r2_hidden(esk10_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( r1_xboole_0(esk34_0,k3_tarski(esk33_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_24,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(esk33_0),esk34_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_23]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
