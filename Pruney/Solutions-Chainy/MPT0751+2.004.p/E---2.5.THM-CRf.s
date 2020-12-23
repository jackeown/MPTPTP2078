%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:34 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 934 expanded)
%              Number of clauses        :   73 ( 412 expanded)
%              Number of leaves         :   16 ( 233 expanded)
%              Depth                    :   16
%              Number of atoms          :  332 (3734 expanded)
%              Number of equality atoms :   32 ( 698 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t42_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( ~ ( ~ v4_ordinal1(X1)
            & ! [X2] :
                ( v3_ordinal1(X2)
               => X1 != k1_ordinal1(X2) ) )
        & ~ ( ? [X2] :
                ( v3_ordinal1(X2)
                & X1 = k1_ordinal1(X2) )
            & v4_ordinal1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_ordinal1)).

fof(connectedness_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
        | r1_ordinal1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(t38_ordinal1,axiom,(
    ! [X1] :
      ~ ! [X2] :
          ( v3_ordinal1(X2)
         => r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(s1_xboole_0__e3_53__ordinal1,axiom,(
    ! [X1] :
    ? [X2] :
    ! [X3] :
      ( r2_hidden(X3,X2)
    <=> ( r2_hidden(X3,X1)
        & v3_ordinal1(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s1_xboole_0__e3_53__ordinal1)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t41_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v4_ordinal1(X1)
      <=> ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X2,X1)
             => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

fof(t33_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
          <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(c_0_16,plain,(
    ! [X29,X30] :
      ( ( ~ r2_hidden(X29,k1_ordinal1(X30))
        | r1_ordinal1(X29,X30)
        | ~ v3_ordinal1(X30)
        | ~ v3_ordinal1(X29) )
      & ( ~ r1_ordinal1(X29,X30)
        | r2_hidden(X29,k1_ordinal1(X30))
        | ~ v3_ordinal1(X30)
        | ~ v3_ordinal1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).

fof(c_0_17,plain,(
    ! [X14] : k1_ordinal1(X14) = k2_xboole_0(X14,k1_tarski(X14)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ( ~ ( ~ v4_ordinal1(X1)
              & ! [X2] :
                  ( v3_ordinal1(X2)
                 => X1 != k1_ordinal1(X2) ) )
          & ~ ( ? [X2] :
                  ( v3_ordinal1(X2)
                  & X1 = k1_ordinal1(X2) )
              & v4_ordinal1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t42_ordinal1])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,negated_conjecture,(
    ! [X39] :
      ( v3_ordinal1(esk5_0)
      & ( v3_ordinal1(esk6_0)
        | ~ v4_ordinal1(esk5_0) )
      & ( esk5_0 = k1_ordinal1(esk6_0)
        | ~ v4_ordinal1(esk5_0) )
      & ( v4_ordinal1(esk5_0)
        | ~ v4_ordinal1(esk5_0) )
      & ( v3_ordinal1(esk6_0)
        | ~ v3_ordinal1(X39)
        | esk5_0 != k1_ordinal1(X39) )
      & ( esk5_0 = k1_ordinal1(esk6_0)
        | ~ v3_ordinal1(X39)
        | esk5_0 != k1_ordinal1(X39) )
      & ( v4_ordinal1(esk5_0)
        | ~ v3_ordinal1(X39)
        | esk5_0 != k1_ordinal1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])])])).

fof(c_0_22,plain,(
    ! [X12,X13] :
      ( ~ v3_ordinal1(X12)
      | ~ v3_ordinal1(X13)
      | r1_ordinal1(X12,X13)
      | r1_ordinal1(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).

fof(c_0_23,plain,(
    ! [X31] :
      ( v3_ordinal1(esk3_1(X31))
      & ~ r2_hidden(esk3_1(X31),X31) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_ordinal1])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r1_ordinal1(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v3_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( r1_ordinal1(X1,X2)
    | r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(esk5_0,k1_tarski(esk5_0)))
    | ~ r1_ordinal1(X1,esk5_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( v3_ordinal1(esk3_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r1_ordinal1(X1,esk5_0)
    | r1_ordinal1(esk5_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25])).

fof(c_0_31,plain,(
    ! [X15,X16] :
      ( ( ~ r1_ordinal1(X15,X16)
        | r1_tarski(X15,X16)
        | ~ v3_ordinal1(X15)
        | ~ v3_ordinal1(X16) )
      & ( ~ r1_tarski(X15,X16)
        | r1_ordinal1(X15,X16)
        | ~ v3_ordinal1(X15)
        | ~ v3_ordinal1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_ordinal1(esk3_1(k2_xboole_0(esk5_0,k1_tarski(esk5_0))),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_33,negated_conjecture,
    ( r1_ordinal1(esk5_0,esk3_1(X1))
    | r1_ordinal1(esk3_1(X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

fof(c_0_34,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r1_ordinal1(esk5_0,esk3_1(k2_xboole_0(esk5_0,k1_tarski(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_37,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_38,plain,(
    ! [X17,X19,X20] :
      ( ( r2_hidden(X19,X17)
        | ~ r2_hidden(X19,esk2_1(X17)) )
      & ( v3_ordinal1(X19)
        | ~ r2_hidden(X19,esk2_1(X17)) )
      & ( ~ r2_hidden(X20,X17)
        | ~ v3_ordinal1(X20)
        | r2_hidden(X20,esk2_1(X17)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[s1_xboole_0__e3_53__ordinal1])])])])])])).

fof(c_0_39,plain,(
    ! [X24,X25] :
      ( ~ v3_ordinal1(X25)
      | ~ r2_hidden(X24,X25)
      | v3_ordinal1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

cnf(c_0_40,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk5_0,esk3_1(k2_xboole_0(esk5_0,k1_tarski(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_29]),c_0_25])])).

fof(c_0_42,plain,(
    ! [X36,X37] :
      ( ~ r2_hidden(X36,X37)
      | ~ r1_tarski(X37,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_44,plain,(
    ! [X33,X34] :
      ( ( ~ v4_ordinal1(X33)
        | ~ v3_ordinal1(X34)
        | ~ r2_hidden(X34,X33)
        | r2_hidden(k1_ordinal1(X34),X33)
        | ~ v3_ordinal1(X33) )
      & ( v3_ordinal1(esk4_1(X33))
        | v4_ordinal1(X33)
        | ~ v3_ordinal1(X33) )
      & ( r2_hidden(esk4_1(X33),X33)
        | v4_ordinal1(X33)
        | ~ v3_ordinal1(X33) )
      & ( ~ r2_hidden(k1_ordinal1(esk4_1(X33)),X33)
        | v4_ordinal1(X33)
        | ~ v3_ordinal1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_ordinal1])])])])])).

fof(c_0_45,plain,(
    ! [X27,X28] :
      ( ( ~ r2_hidden(X27,X28)
        | r1_ordinal1(k1_ordinal1(X27),X28)
        | ~ v3_ordinal1(X28)
        | ~ v3_ordinal1(X27) )
      & ( ~ r1_ordinal1(k1_ordinal1(X27),X28)
        | r2_hidden(X27,X28)
        | ~ v3_ordinal1(X28)
        | ~ v3_ordinal1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,esk2_1(X2))
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(X1,esk3_1(k2_xboole_0(esk5_0,k1_tarski(esk5_0))))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( v3_ordinal1(esk6_0)
    | ~ v4_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_53,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r2_hidden(X1,k1_ordinal1(X2))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_54,negated_conjecture,
    ( esk5_0 = k1_ordinal1(esk6_0)
    | ~ v4_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_55,plain,
    ( r2_hidden(k1_ordinal1(X2),X1)
    | ~ v4_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_56,plain,(
    ! [X21] : r2_hidden(X21,k1_ordinal1(X21)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

fof(c_0_57,plain,(
    ! [X22,X23] :
      ( ( ~ r2_hidden(X22,k1_ordinal1(X23))
        | r2_hidden(X22,X23)
        | X22 = X23 )
      & ( ~ r2_hidden(X22,X23)
        | r2_hidden(X22,k1_ordinal1(X23)) )
      & ( X22 != X23
        | r2_hidden(X22,k1_ordinal1(X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

cnf(c_0_58,plain,
    ( r1_ordinal1(k1_ordinal1(X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,esk2_1(X2))
    | ~ v3_ordinal1(esk1_2(X1,esk2_1(X2)))
    | ~ r2_hidden(esk1_2(X1,esk2_1(X2)),X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_60,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_61,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_29])])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk2_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(esk6_0,k1_tarski(esk6_0)))
    | ~ v4_ordinal1(esk5_0)
    | ~ r1_ordinal1(X1,esk6_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_52])).

cnf(c_0_65,plain,
    ( r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_53,c_0_20])).

cnf(c_0_66,negated_conjecture,
    ( esk5_0 = k2_xboole_0(esk6_0,k1_tarski(esk6_0))
    | ~ v4_ordinal1(esk5_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_20])).

cnf(c_0_67,plain,
    ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X1)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ v4_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_55,c_0_20])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_70,plain,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_58,c_0_20])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,esk2_1(X1))
    | ~ v3_ordinal1(esk1_2(X1,esk2_1(X1))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_72,negated_conjecture,
    ( v3_ordinal1(esk1_2(esk5_0,X1))
    | r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_60])).

cnf(c_0_73,plain,
    ( r2_hidden(esk1_2(esk2_1(X1),X2),X1)
    | r1_tarski(esk2_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_60])).

cnf(c_0_74,negated_conjecture,
    ( ~ v4_ordinal1(esk5_0)
    | ~ r1_ordinal1(k2_xboole_0(esk6_0,k1_tarski(esk6_0)),esk6_0)
    | ~ v3_ordinal1(k2_xboole_0(esk6_0,k1_tarski(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_75,negated_conjecture,
    ( r1_ordinal1(X1,esk6_0)
    | ~ v4_ordinal1(esk5_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_52])).

cnf(c_0_76,plain,
    ( r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v4_ordinal1(X2)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_67,c_0_48])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_68,c_0_20])).

cnf(c_0_78,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_69,c_0_20])).

cnf(c_0_79,plain,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_70,c_0_48])).

cnf(c_0_80,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | v4_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_81,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(esk5_0,esk2_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_83,plain,
    ( r1_tarski(esk2_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_73])).

cnf(c_0_84,negated_conjecture,
    ( ~ v4_ordinal1(esk5_0)
    | ~ r2_hidden(k2_xboole_0(esk6_0,k1_tarski(esk6_0)),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_61])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk5_0)
    | ~ v4_ordinal1(esk5_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_25])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0)
    | ~ v4_ordinal1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_66])).

cnf(c_0_87,plain,
    ( v4_ordinal1(X1)
    | ~ r2_hidden(k1_ordinal1(esk4_1(X1)),X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_88,negated_conjecture,
    ( X1 = esk5_0
    | r2_hidden(X1,esk5_0)
    | ~ r1_ordinal1(X1,esk5_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_28])).

cnf(c_0_89,negated_conjecture,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),esk5_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_25])).

cnf(c_0_90,plain,
    ( v4_ordinal1(esk2_1(X1))
    | r2_hidden(esk4_1(esk2_1(X1)),X1)
    | ~ v3_ordinal1(esk2_1(X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_80])).

cnf(c_0_91,negated_conjecture,
    ( esk2_1(esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])])).

cnf(c_0_92,negated_conjecture,
    ( ~ v4_ordinal1(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])).

fof(c_0_93,plain,(
    ! [X26] :
      ( ~ v3_ordinal1(X26)
      | v3_ordinal1(k1_ordinal1(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

cnf(c_0_94,plain,
    ( v4_ordinal1(X1)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(k2_xboole_0(esk4_1(X1),k1_tarski(esk4_1(X1))),X1) ),
    inference(rw,[status(thm)],[c_0_87,c_0_20])).

cnf(c_0_95,negated_conjecture,
    ( k2_xboole_0(X1,k1_tarski(X1)) = esk5_0
    | r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk5_0)
    | ~ v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk4_1(esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_25])]),c_0_92])).

cnf(c_0_97,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( v4_ordinal1(esk5_0)
    | v3_ordinal1(esk4_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_80]),c_0_25])])).

cnf(c_0_99,negated_conjecture,
    ( v4_ordinal1(esk5_0)
    | ~ v3_ordinal1(X1)
    | esk5_0 != k1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_100,negated_conjecture,
    ( k2_xboole_0(esk4_1(esk5_0),k1_tarski(esk4_1(esk5_0))) = esk5_0
    | ~ v3_ordinal1(k2_xboole_0(esk4_1(esk5_0),k1_tarski(esk4_1(esk5_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_25]),c_0_96])]),c_0_92])).

cnf(c_0_101,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_97,c_0_20])).

cnf(c_0_102,negated_conjecture,
    ( v3_ordinal1(esk4_1(esk5_0)) ),
    inference(sr,[status(thm)],[c_0_98,c_0_92])).

cnf(c_0_103,negated_conjecture,
    ( v4_ordinal1(esk5_0)
    | esk5_0 != k2_xboole_0(X1,k1_tarski(X1))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_99,c_0_20])).

cnf(c_0_104,negated_conjecture,
    ( k2_xboole_0(esk4_1(esk5_0),k1_tarski(esk4_1(esk5_0))) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102])])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_102])]),c_0_92]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:47:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.49  # AutoSched0-Mode selected heuristic G_E___208_C12_11_nc_F1_SE_CS_SP_PS_S063N
% 0.20/0.49  # and selection function SelectMaxLComplexAvoidPosUPred.
% 0.20/0.49  #
% 0.20/0.49  # Preprocessing time       : 0.029 s
% 0.20/0.49  # Presaturation interreduction done
% 0.20/0.49  
% 0.20/0.49  # Proof found!
% 0.20/0.49  # SZS status Theorem
% 0.20/0.49  # SZS output start CNFRefutation
% 0.20/0.49  fof(t34_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 0.20/0.49  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.20/0.49  fof(t42_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>(~((~(v4_ordinal1(X1))&![X2]:(v3_ordinal1(X2)=>X1!=k1_ordinal1(X2))))&~((?[X2]:(v3_ordinal1(X2)&X1=k1_ordinal1(X2))&v4_ordinal1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_ordinal1)).
% 0.20/0.49  fof(connectedness_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 0.20/0.49  fof(t38_ordinal1, axiom, ![X1]:~(![X2]:(v3_ordinal1(X2)=>r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_ordinal1)).
% 0.20/0.49  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.20/0.49  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.49  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.49  fof(s1_xboole_0__e3_53__ordinal1, axiom, ![X1]:?[X2]:![X3]:(r2_hidden(X3,X2)<=>(r2_hidden(X3,X1)&v3_ordinal1(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s1_xboole_0__e3_53__ordinal1)).
% 0.20/0.49  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 0.20/0.49  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.49  fof(t41_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_ordinal1)).
% 0.20/0.49  fof(t33_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 0.20/0.49  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 0.20/0.49  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 0.20/0.49  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 0.20/0.49  fof(c_0_16, plain, ![X29, X30]:((~r2_hidden(X29,k1_ordinal1(X30))|r1_ordinal1(X29,X30)|~v3_ordinal1(X30)|~v3_ordinal1(X29))&(~r1_ordinal1(X29,X30)|r2_hidden(X29,k1_ordinal1(X30))|~v3_ordinal1(X30)|~v3_ordinal1(X29))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).
% 0.20/0.49  fof(c_0_17, plain, ![X14]:k1_ordinal1(X14)=k2_xboole_0(X14,k1_tarski(X14)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.20/0.49  fof(c_0_18, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>(~((~(v4_ordinal1(X1))&![X2]:(v3_ordinal1(X2)=>X1!=k1_ordinal1(X2))))&~((?[X2]:(v3_ordinal1(X2)&X1=k1_ordinal1(X2))&v4_ordinal1(X1)))))), inference(assume_negation,[status(cth)],[t42_ordinal1])).
% 0.20/0.49  cnf(c_0_19, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.49  cnf(c_0_20, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.49  fof(c_0_21, negated_conjecture, ![X39]:(v3_ordinal1(esk5_0)&((((v3_ordinal1(esk6_0)|~v4_ordinal1(esk5_0))&(esk5_0=k1_ordinal1(esk6_0)|~v4_ordinal1(esk5_0)))&(v4_ordinal1(esk5_0)|~v4_ordinal1(esk5_0)))&(((v3_ordinal1(esk6_0)|(~v3_ordinal1(X39)|esk5_0!=k1_ordinal1(X39)))&(esk5_0=k1_ordinal1(esk6_0)|(~v3_ordinal1(X39)|esk5_0!=k1_ordinal1(X39))))&(v4_ordinal1(esk5_0)|(~v3_ordinal1(X39)|esk5_0!=k1_ordinal1(X39)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])])])).
% 0.20/0.49  fof(c_0_22, plain, ![X12, X13]:(~v3_ordinal1(X12)|~v3_ordinal1(X13)|(r1_ordinal1(X12,X13)|r1_ordinal1(X13,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).
% 0.20/0.49  fof(c_0_23, plain, ![X31]:(v3_ordinal1(esk3_1(X31))&~r2_hidden(esk3_1(X31),X31)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_ordinal1])])])).
% 0.20/0.49  cnf(c_0_24, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r1_ordinal1(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.49  cnf(c_0_25, negated_conjecture, (v3_ordinal1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.49  cnf(c_0_26, plain, (r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.49  cnf(c_0_27, plain, (~r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.49  cnf(c_0_28, negated_conjecture, (r2_hidden(X1,k2_xboole_0(esk5_0,k1_tarski(esk5_0)))|~r1_ordinal1(X1,esk5_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.49  cnf(c_0_29, plain, (v3_ordinal1(esk3_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.49  cnf(c_0_30, negated_conjecture, (r1_ordinal1(X1,esk5_0)|r1_ordinal1(esk5_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_25])).
% 0.20/0.49  fof(c_0_31, plain, ![X15, X16]:((~r1_ordinal1(X15,X16)|r1_tarski(X15,X16)|(~v3_ordinal1(X15)|~v3_ordinal1(X16)))&(~r1_tarski(X15,X16)|r1_ordinal1(X15,X16)|(~v3_ordinal1(X15)|~v3_ordinal1(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.20/0.49  cnf(c_0_32, negated_conjecture, (~r1_ordinal1(esk3_1(k2_xboole_0(esk5_0,k1_tarski(esk5_0))),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.20/0.49  cnf(c_0_33, negated_conjecture, (r1_ordinal1(esk5_0,esk3_1(X1))|r1_ordinal1(esk3_1(X1),esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_29])).
% 0.20/0.49  fof(c_0_34, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.49  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.49  cnf(c_0_36, negated_conjecture, (r1_ordinal1(esk5_0,esk3_1(k2_xboole_0(esk5_0,k1_tarski(esk5_0))))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.49  fof(c_0_37, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.49  fof(c_0_38, plain, ![X17, X19, X20]:(((r2_hidden(X19,X17)|~r2_hidden(X19,esk2_1(X17)))&(v3_ordinal1(X19)|~r2_hidden(X19,esk2_1(X17))))&(~r2_hidden(X20,X17)|~v3_ordinal1(X20)|r2_hidden(X20,esk2_1(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[s1_xboole_0__e3_53__ordinal1])])])])])])).
% 0.20/0.49  fof(c_0_39, plain, ![X24, X25]:(~v3_ordinal1(X25)|(~r2_hidden(X24,X25)|v3_ordinal1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 0.20/0.49  cnf(c_0_40, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.49  cnf(c_0_41, negated_conjecture, (r1_tarski(esk5_0,esk3_1(k2_xboole_0(esk5_0,k1_tarski(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_29]), c_0_25])])).
% 0.20/0.49  fof(c_0_42, plain, ![X36, X37]:(~r2_hidden(X36,X37)|~r1_tarski(X37,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.49  cnf(c_0_43, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.49  fof(c_0_44, plain, ![X33, X34]:((~v4_ordinal1(X33)|(~v3_ordinal1(X34)|(~r2_hidden(X34,X33)|r2_hidden(k1_ordinal1(X34),X33)))|~v3_ordinal1(X33))&((v3_ordinal1(esk4_1(X33))|v4_ordinal1(X33)|~v3_ordinal1(X33))&((r2_hidden(esk4_1(X33),X33)|v4_ordinal1(X33)|~v3_ordinal1(X33))&(~r2_hidden(k1_ordinal1(esk4_1(X33)),X33)|v4_ordinal1(X33)|~v3_ordinal1(X33))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_ordinal1])])])])])).
% 0.20/0.49  fof(c_0_45, plain, ![X27, X28]:((~r2_hidden(X27,X28)|r1_ordinal1(k1_ordinal1(X27),X28)|~v3_ordinal1(X28)|~v3_ordinal1(X27))&(~r1_ordinal1(k1_ordinal1(X27),X28)|r2_hidden(X27,X28)|~v3_ordinal1(X28)|~v3_ordinal1(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).
% 0.20/0.49  cnf(c_0_46, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.49  cnf(c_0_47, plain, (r2_hidden(X1,esk2_1(X2))|~r2_hidden(X1,X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.49  cnf(c_0_48, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.49  cnf(c_0_49, negated_conjecture, (r2_hidden(X1,esk3_1(k2_xboole_0(esk5_0,k1_tarski(esk5_0))))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.49  cnf(c_0_50, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.49  cnf(c_0_51, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_43])).
% 0.20/0.49  cnf(c_0_52, negated_conjecture, (v3_ordinal1(esk6_0)|~v4_ordinal1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.49  cnf(c_0_53, plain, (r1_ordinal1(X1,X2)|~r2_hidden(X1,k1_ordinal1(X2))|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.49  cnf(c_0_54, negated_conjecture, (esk5_0=k1_ordinal1(esk6_0)|~v4_ordinal1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.49  cnf(c_0_55, plain, (r2_hidden(k1_ordinal1(X2),X1)|~v4_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X2,X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.49  fof(c_0_56, plain, ![X21]:r2_hidden(X21,k1_ordinal1(X21)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 0.20/0.49  fof(c_0_57, plain, ![X22, X23]:((~r2_hidden(X22,k1_ordinal1(X23))|(r2_hidden(X22,X23)|X22=X23))&((~r2_hidden(X22,X23)|r2_hidden(X22,k1_ordinal1(X23)))&(X22!=X23|r2_hidden(X22,k1_ordinal1(X23))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 0.20/0.49  cnf(c_0_58, plain, (r1_ordinal1(k1_ordinal1(X1),X2)|~r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.49  cnf(c_0_59, plain, (r1_tarski(X1,esk2_1(X2))|~v3_ordinal1(esk1_2(X1,esk2_1(X2)))|~r2_hidden(esk1_2(X1,esk2_1(X2)),X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.49  cnf(c_0_60, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.49  cnf(c_0_61, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_29])])).
% 0.20/0.49  cnf(c_0_62, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,esk2_1(X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.49  cnf(c_0_63, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.49  cnf(c_0_64, negated_conjecture, (r2_hidden(X1,k2_xboole_0(esk6_0,k1_tarski(esk6_0)))|~v4_ordinal1(esk5_0)|~r1_ordinal1(X1,esk6_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_52])).
% 0.20/0.49  cnf(c_0_65, plain, (r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_53, c_0_20])).
% 0.20/0.49  cnf(c_0_66, negated_conjecture, (esk5_0=k2_xboole_0(esk6_0,k1_tarski(esk6_0))|~v4_ordinal1(esk5_0)), inference(rw,[status(thm)],[c_0_54, c_0_20])).
% 0.20/0.49  cnf(c_0_67, plain, (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X1)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~v4_ordinal1(X1)|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_55, c_0_20])).
% 0.20/0.49  cnf(c_0_68, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.49  cnf(c_0_69, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.49  cnf(c_0_70, plain, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_58, c_0_20])).
% 0.20/0.49  cnf(c_0_71, plain, (r1_tarski(X1,esk2_1(X1))|~v3_ordinal1(esk1_2(X1,esk2_1(X1)))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.49  cnf(c_0_72, negated_conjecture, (v3_ordinal1(esk1_2(esk5_0,X1))|r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_61, c_0_60])).
% 0.20/0.49  cnf(c_0_73, plain, (r2_hidden(esk1_2(esk2_1(X1),X2),X1)|r1_tarski(esk2_1(X1),X2)), inference(spm,[status(thm)],[c_0_62, c_0_60])).
% 0.20/0.49  cnf(c_0_74, negated_conjecture, (~v4_ordinal1(esk5_0)|~r1_ordinal1(k2_xboole_0(esk6_0,k1_tarski(esk6_0)),esk6_0)|~v3_ordinal1(k2_xboole_0(esk6_0,k1_tarski(esk6_0)))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.49  cnf(c_0_75, negated_conjecture, (r1_ordinal1(X1,esk6_0)|~v4_ordinal1(esk5_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_52])).
% 0.20/0.49  cnf(c_0_76, plain, (r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v4_ordinal1(X2)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_67, c_0_48])).
% 0.20/0.49  cnf(c_0_77, plain, (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_68, c_0_20])).
% 0.20/0.49  cnf(c_0_78, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_69, c_0_20])).
% 0.20/0.49  cnf(c_0_79, plain, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_70, c_0_48])).
% 0.20/0.49  cnf(c_0_80, plain, (r2_hidden(esk4_1(X1),X1)|v4_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.49  cnf(c_0_81, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.49  cnf(c_0_82, negated_conjecture, (r1_tarski(esk5_0,esk2_1(esk5_0))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.49  cnf(c_0_83, plain, (r1_tarski(esk2_1(X1),X1)), inference(spm,[status(thm)],[c_0_46, c_0_73])).
% 0.20/0.49  cnf(c_0_84, negated_conjecture, (~v4_ordinal1(esk5_0)|~r2_hidden(k2_xboole_0(esk6_0,k1_tarski(esk6_0)),esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_61])).
% 0.20/0.49  cnf(c_0_85, negated_conjecture, (r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk5_0)|~v4_ordinal1(esk5_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_76, c_0_25])).
% 0.20/0.49  cnf(c_0_86, negated_conjecture, (r2_hidden(esk6_0,esk5_0)|~v4_ordinal1(esk5_0)), inference(spm,[status(thm)],[c_0_77, c_0_66])).
% 0.20/0.49  cnf(c_0_87, plain, (v4_ordinal1(X1)|~r2_hidden(k1_ordinal1(esk4_1(X1)),X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.49  cnf(c_0_88, negated_conjecture, (X1=esk5_0|r2_hidden(X1,esk5_0)|~r1_ordinal1(X1,esk5_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_78, c_0_28])).
% 0.20/0.49  cnf(c_0_89, negated_conjecture, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),esk5_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_79, c_0_25])).
% 0.20/0.49  cnf(c_0_90, plain, (v4_ordinal1(esk2_1(X1))|r2_hidden(esk4_1(esk2_1(X1)),X1)|~v3_ordinal1(esk2_1(X1))), inference(spm,[status(thm)],[c_0_62, c_0_80])).
% 0.20/0.49  cnf(c_0_91, negated_conjecture, (esk2_1(esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83])])).
% 0.20/0.49  cnf(c_0_92, negated_conjecture, (~v4_ordinal1(esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])).
% 0.20/0.49  fof(c_0_93, plain, ![X26]:(~v3_ordinal1(X26)|v3_ordinal1(k1_ordinal1(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 0.20/0.49  cnf(c_0_94, plain, (v4_ordinal1(X1)|~v3_ordinal1(X1)|~r2_hidden(k2_xboole_0(esk4_1(X1),k1_tarski(esk4_1(X1))),X1)), inference(rw,[status(thm)],[c_0_87, c_0_20])).
% 0.20/0.49  cnf(c_0_95, negated_conjecture, (k2_xboole_0(X1,k1_tarski(X1))=esk5_0|r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk5_0)|~v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.20/0.49  cnf(c_0_96, negated_conjecture, (r2_hidden(esk4_1(esk5_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_25])]), c_0_92])).
% 0.20/0.49  cnf(c_0_97, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.20/0.49  cnf(c_0_98, negated_conjecture, (v4_ordinal1(esk5_0)|v3_ordinal1(esk4_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_80]), c_0_25])])).
% 0.20/0.49  cnf(c_0_99, negated_conjecture, (v4_ordinal1(esk5_0)|~v3_ordinal1(X1)|esk5_0!=k1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.49  cnf(c_0_100, negated_conjecture, (k2_xboole_0(esk4_1(esk5_0),k1_tarski(esk4_1(esk5_0)))=esk5_0|~v3_ordinal1(k2_xboole_0(esk4_1(esk5_0),k1_tarski(esk4_1(esk5_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_25]), c_0_96])]), c_0_92])).
% 0.20/0.49  cnf(c_0_101, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_97, c_0_20])).
% 0.20/0.49  cnf(c_0_102, negated_conjecture, (v3_ordinal1(esk4_1(esk5_0))), inference(sr,[status(thm)],[c_0_98, c_0_92])).
% 0.20/0.49  cnf(c_0_103, negated_conjecture, (v4_ordinal1(esk5_0)|esk5_0!=k2_xboole_0(X1,k1_tarski(X1))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_99, c_0_20])).
% 0.20/0.49  cnf(c_0_104, negated_conjecture, (k2_xboole_0(esk4_1(esk5_0),k1_tarski(esk4_1(esk5_0)))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_102])])).
% 0.20/0.49  cnf(c_0_105, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_102])]), c_0_92]), ['proof']).
% 0.20/0.49  # SZS output end CNFRefutation
% 0.20/0.49  # Proof object total steps             : 106
% 0.20/0.49  # Proof object clause steps            : 73
% 0.20/0.49  # Proof object formula steps           : 33
% 0.20/0.49  # Proof object conjectures             : 36
% 0.20/0.49  # Proof object clause conjectures      : 33
% 0.20/0.49  # Proof object formula conjectures     : 3
% 0.20/0.49  # Proof object initial clauses used    : 27
% 0.20/0.49  # Proof object initial formulas used   : 16
% 0.20/0.49  # Proof object generating inferences   : 32
% 0.20/0.49  # Proof object simplifying inferences  : 40
% 0.20/0.49  # Training examples: 0 positive, 0 negative
% 0.20/0.49  # Parsed axioms                        : 16
% 0.20/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.49  # Initial clauses                      : 37
% 0.20/0.49  # Removed in clause preprocessing      : 2
% 0.20/0.49  # Initial clauses in saturation        : 35
% 0.20/0.49  # Processed clauses                    : 1789
% 0.20/0.49  # ...of these trivial                  : 7
% 0.20/0.49  # ...subsumed                          : 1075
% 0.20/0.49  # ...remaining for further processing  : 707
% 0.20/0.49  # Other redundant clauses eliminated   : 3
% 0.20/0.49  # Clauses deleted for lack of memory   : 0
% 0.20/0.49  # Backward-subsumed                    : 23
% 0.20/0.49  # Backward-rewritten                   : 153
% 0.20/0.49  # Generated clauses                    : 3925
% 0.20/0.49  # ...of the previous two non-trivial   : 3802
% 0.20/0.49  # Contextual simplify-reflections      : 68
% 0.20/0.49  # Paramodulations                      : 3917
% 0.20/0.49  # Factorizations                       : 0
% 0.20/0.49  # Equation resolutions                 : 3
% 0.20/0.49  # Propositional unsat checks           : 0
% 0.20/0.49  #    Propositional check models        : 0
% 0.20/0.49  #    Propositional check unsatisfiable : 0
% 0.20/0.49  #    Propositional clauses             : 0
% 0.20/0.49  #    Propositional clauses after purity: 0
% 0.20/0.49  #    Propositional unsat core size     : 0
% 0.20/0.49  #    Propositional preprocessing time  : 0.000
% 0.20/0.49  #    Propositional encoding time       : 0.000
% 0.20/0.49  #    Propositional solver time         : 0.000
% 0.20/0.49  #    Success case prop preproc time    : 0.000
% 0.20/0.49  #    Success case prop encoding time   : 0.000
% 0.20/0.49  #    Success case prop solver time     : 0.000
% 0.20/0.49  # Current number of processed clauses  : 490
% 0.20/0.49  #    Positive orientable unit clauses  : 36
% 0.20/0.49  #    Positive unorientable unit clauses: 0
% 0.20/0.49  #    Negative unit clauses             : 81
% 0.20/0.49  #    Non-unit-clauses                  : 373
% 0.20/0.49  # Current number of unprocessed clauses: 1730
% 0.20/0.49  # ...number of literals in the above   : 4820
% 0.20/0.49  # Current number of archived formulas  : 0
% 0.20/0.49  # Current number of archived clauses   : 215
% 0.20/0.49  # Clause-clause subsumption calls (NU) : 29000
% 0.20/0.49  # Rec. Clause-clause subsumption calls : 15007
% 0.20/0.49  # Non-unit clause-clause subsumptions  : 423
% 0.20/0.49  # Unit Clause-clause subsumption calls : 5866
% 0.20/0.49  # Rewrite failures with RHS unbound    : 0
% 0.20/0.49  # BW rewrite match attempts            : 87
% 0.20/0.49  # BW rewrite match successes           : 60
% 0.20/0.49  # Condensation attempts                : 0
% 0.20/0.49  # Condensation successes               : 0
% 0.20/0.49  # Termbank termtop insertions          : 82902
% 0.20/0.49  
% 0.20/0.49  # -------------------------------------------------
% 0.20/0.49  # User time                : 0.145 s
% 0.20/0.49  # System time              : 0.006 s
% 0.20/0.49  # Total time               : 0.151 s
% 0.20/0.49  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
