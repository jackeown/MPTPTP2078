%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0384+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:32 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    9 (   9 expanded)
%              Number of clauses        :    4 (   4 expanded)
%              Number of leaves         :    2 (   2 expanded)
%              Depth                    :    4
%              Number of atoms          :   50 (  50 expanded)
%              Number of equality atoms :   32 (  32 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(t2_setfam_1,conjecture,(
    k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_setfam_1)).

fof(c_0_2,plain,(
    ! [X5,X6,X7,X8,X9,X11,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X7,X6)
        | ~ r2_hidden(X8,X5)
        | r2_hidden(X7,X8)
        | X6 != k1_setfam_1(X5)
        | X5 = k1_xboole_0 )
      & ( r2_hidden(esk1_3(X5,X6,X9),X5)
        | r2_hidden(X9,X6)
        | X6 != k1_setfam_1(X5)
        | X5 = k1_xboole_0 )
      & ( ~ r2_hidden(X9,esk1_3(X5,X6,X9))
        | r2_hidden(X9,X6)
        | X6 != k1_setfam_1(X5)
        | X5 = k1_xboole_0 )
      & ( r2_hidden(esk3_2(X5,X11),X5)
        | ~ r2_hidden(esk2_2(X5,X11),X11)
        | X11 = k1_setfam_1(X5)
        | X5 = k1_xboole_0 )
      & ( ~ r2_hidden(esk2_2(X5,X11),esk3_2(X5,X11))
        | ~ r2_hidden(esk2_2(X5,X11),X11)
        | X11 = k1_setfam_1(X5)
        | X5 = k1_xboole_0 )
      & ( r2_hidden(esk2_2(X5,X11),X11)
        | ~ r2_hidden(X14,X5)
        | r2_hidden(esk2_2(X5,X11),X14)
        | X11 = k1_setfam_1(X5)
        | X5 = k1_xboole_0 )
      & ( X16 != k1_setfam_1(X15)
        | X16 = k1_xboole_0
        | X15 != k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | X17 = k1_setfam_1(X15)
        | X15 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

fof(c_0_3,negated_conjecture,(
    k1_setfam_1(k1_xboole_0) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t2_setfam_1])).

cnf(c_0_4,plain,
    ( X1 = k1_setfam_1(X2)
    | X1 != k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

fof(c_0_5,negated_conjecture,(
    k1_setfam_1(k1_xboole_0) != k1_xboole_0 ),
    inference(fof_simplification,[status(thm)],[c_0_3])).

cnf(c_0_6,plain,
    ( X1 = k1_setfam_1(k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k1_setfam_1(k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_6]),c_0_7]),
    [proof]).

%------------------------------------------------------------------------------
