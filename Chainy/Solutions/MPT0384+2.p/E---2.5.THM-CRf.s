%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0384+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:44 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :    8 (   8 expanded)
%              Number of clauses        :    3 (   3 expanded)
%              Number of leaves         :    2 (   2 expanded)
%              Depth                    :    4
%              Number of atoms          :   48 (  48 expanded)
%              Number of equality atoms :   30 (  30 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_setfam_1,conjecture,(
    k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_setfam_1)).

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

fof(c_0_2,negated_conjecture,(
    k1_setfam_1(k1_xboole_0) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t2_setfam_1])).

fof(c_0_3,plain,(
    ! [X1826,X1827,X1828,X1829,X1830,X1832,X1835,X1836,X1837,X1838] :
      ( ( ~ r2_hidden(X1828,X1827)
        | ~ r2_hidden(X1829,X1826)
        | r2_hidden(X1828,X1829)
        | X1827 != k1_setfam_1(X1826)
        | X1826 = k1_xboole_0 )
      & ( r2_hidden(esk82_3(X1826,X1827,X1830),X1826)
        | r2_hidden(X1830,X1827)
        | X1827 != k1_setfam_1(X1826)
        | X1826 = k1_xboole_0 )
      & ( ~ r2_hidden(X1830,esk82_3(X1826,X1827,X1830))
        | r2_hidden(X1830,X1827)
        | X1827 != k1_setfam_1(X1826)
        | X1826 = k1_xboole_0 )
      & ( r2_hidden(esk84_2(X1826,X1832),X1826)
        | ~ r2_hidden(esk83_2(X1826,X1832),X1832)
        | X1832 = k1_setfam_1(X1826)
        | X1826 = k1_xboole_0 )
      & ( ~ r2_hidden(esk83_2(X1826,X1832),esk84_2(X1826,X1832))
        | ~ r2_hidden(esk83_2(X1826,X1832),X1832)
        | X1832 = k1_setfam_1(X1826)
        | X1826 = k1_xboole_0 )
      & ( r2_hidden(esk83_2(X1826,X1832),X1832)
        | ~ r2_hidden(X1835,X1826)
        | r2_hidden(esk83_2(X1826,X1832),X1835)
        | X1832 = k1_setfam_1(X1826)
        | X1826 = k1_xboole_0 )
      & ( X1837 != k1_setfam_1(X1836)
        | X1837 = k1_xboole_0
        | X1836 != k1_xboole_0 )
      & ( X1838 != k1_xboole_0
        | X1838 = k1_setfam_1(X1836)
        | X1836 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

fof(c_0_4,negated_conjecture,(
    k1_setfam_1(k1_xboole_0) != k1_xboole_0 ),
    inference(fof_simplification,[status(thm)],[c_0_2])).

cnf(c_0_5,plain,
    ( X1 = k1_xboole_0
    | X1 != k1_setfam_1(X2)
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( k1_setfam_1(k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_5])]),c_0_6]),
    [proof]).
%------------------------------------------------------------------------------
