%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0003+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:30 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 202 expanded)
%              Number of clauses        :   35 (  98 expanded)
%              Number of leaves         :    8 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  163 ( 798 expanded)
%              Number of equality atoms :   38 ( 183 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t3_xboole_0,conjecture,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_8,plain,(
    ! [X26,X27,X28,X29,X30,X31,X32,X33] :
      ( ( r2_hidden(X29,X26)
        | ~ r2_hidden(X29,X28)
        | X28 != k3_xboole_0(X26,X27) )
      & ( r2_hidden(X29,X27)
        | ~ r2_hidden(X29,X28)
        | X28 != k3_xboole_0(X26,X27) )
      & ( ~ r2_hidden(X30,X26)
        | ~ r2_hidden(X30,X27)
        | r2_hidden(X30,X28)
        | X28 != k3_xboole_0(X26,X27) )
      & ( ~ r2_hidden(esk3_3(X31,X32,X33),X33)
        | ~ r2_hidden(esk3_3(X31,X32,X33),X31)
        | ~ r2_hidden(esk3_3(X31,X32,X33),X32)
        | X33 = k3_xboole_0(X31,X32) )
      & ( r2_hidden(esk3_3(X31,X32,X33),X31)
        | r2_hidden(esk3_3(X31,X32,X33),X33)
        | X33 = k3_xboole_0(X31,X32) )
      & ( r2_hidden(esk3_3(X31,X32,X33),X32)
        | r2_hidden(esk3_3(X31,X32,X33),X33)
        | X33 = k3_xboole_0(X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_9,plain,(
    ! [X50] :
      ( ~ v1_xboole_0(X50)
      | X50 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_10,plain,(
    ! [X13,X14,X15] :
      ( ( ~ v1_xboole_0(X13)
        | ~ r2_hidden(X14,X13) )
      & ( r2_hidden(esk1_1(X15),X15)
        | v1_xboole_0(X15) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ~ ( ~ r1_xboole_0(X1,X2)
            & ! [X3] :
                ~ ( r2_hidden(X3,X1)
                  & r2_hidden(X3,X2) ) )
        & ~ ( ? [X3] :
                ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) )
            & r1_xboole_0(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t3_xboole_0])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,negated_conjecture,(
    ! [X67] :
      ( ( r2_hidden(esk11_0,esk9_0)
        | ~ r1_xboole_0(esk9_0,esk10_0) )
      & ( r2_hidden(esk11_0,esk10_0)
        | ~ r1_xboole_0(esk9_0,esk10_0) )
      & ( r1_xboole_0(esk9_0,esk10_0)
        | ~ r1_xboole_0(esk9_0,esk10_0) )
      & ( r2_hidden(esk11_0,esk9_0)
        | ~ r2_hidden(X67,esk9_0)
        | ~ r2_hidden(X67,esk10_0) )
      & ( r2_hidden(esk11_0,esk10_0)
        | ~ r2_hidden(X67,esk9_0)
        | ~ r2_hidden(X67,esk10_0) )
      & ( r1_xboole_0(esk9_0,esk10_0)
        | ~ r2_hidden(X67,esk9_0)
        | ~ r2_hidden(X67,esk10_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( r1_xboole_0(esk9_0,esk10_0)
    | ~ r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk1_1(k3_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_23,plain,(
    ! [X46,X47] :
      ( ( ~ r1_xboole_0(X46,X47)
        | k3_xboole_0(X46,X47) = k1_xboole_0 )
      & ( k3_xboole_0(X46,X47) != k1_xboole_0
        | r1_xboole_0(X46,X47) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_24,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41,X42] :
      ( ( r2_hidden(X38,X35)
        | ~ r2_hidden(X38,X37)
        | X37 != k4_xboole_0(X35,X36) )
      & ( ~ r2_hidden(X38,X36)
        | ~ r2_hidden(X38,X37)
        | X37 != k4_xboole_0(X35,X36) )
      & ( ~ r2_hidden(X39,X35)
        | r2_hidden(X39,X36)
        | r2_hidden(X39,X37)
        | X37 != k4_xboole_0(X35,X36) )
      & ( ~ r2_hidden(esk4_3(X40,X41,X42),X42)
        | ~ r2_hidden(esk4_3(X40,X41,X42),X40)
        | r2_hidden(esk4_3(X40,X41,X42),X41)
        | X42 = k4_xboole_0(X40,X41) )
      & ( r2_hidden(esk4_3(X40,X41,X42),X40)
        | r2_hidden(esk4_3(X40,X41,X42),X42)
        | X42 = k4_xboole_0(X40,X41) )
      & ( ~ r2_hidden(esk4_3(X40,X41,X42),X41)
        | r2_hidden(esk4_3(X40,X41,X42),X42)
        | X42 = k4_xboole_0(X40,X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_25,negated_conjecture,
    ( k3_xboole_0(X1,esk9_0) = k1_xboole_0
    | r1_xboole_0(esk9_0,esk10_0)
    | ~ r2_hidden(esk1_1(k3_xboole_0(X1,esk9_0)),esk10_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk1_1(k3_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_17])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( k3_xboole_0(esk9_0,esk10_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk11_0,esk10_0)
    | ~ r1_xboole_0(esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( r1_xboole_0(esk9_0,esk10_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk1_1(k4_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_17])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk11_0,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk11_0,esk9_0)
    | ~ r1_xboole_0(esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_hidden(esk11_0,k4_xboole_0(X1,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk11_0,k3_xboole_0(X1,esk10_0))
    | ~ r2_hidden(esk11_0,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk11_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_35])])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(esk11_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_31]),c_0_49]),
    [proof]).
%------------------------------------------------------------------------------
