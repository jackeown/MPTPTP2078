%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:34 EST 2020

% Result     : Theorem 47.54s
% Output     : CNFRefutation 47.54s
% Verified   : 
% Statistics : Number of formulae       :  101 (4441 expanded)
%              Number of clauses        :   74 (2038 expanded)
%              Number of leaves         :   13 (1044 expanded)
%              Depth                    :   26
%              Number of atoms          :  308 (19029 expanded)
%              Number of equality atoms :   30 (3800 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_ordinal1)).

fof(t41_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v4_ordinal1(X1)
      <=> ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X2,X1)
             => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(t34_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t33_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
          <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X45,X46] :
      ( ( ~ v4_ordinal1(X45)
        | ~ v3_ordinal1(X46)
        | ~ r2_hidden(X46,X45)
        | r2_hidden(k1_ordinal1(X46),X45)
        | ~ v3_ordinal1(X45) )
      & ( v3_ordinal1(esk7_1(X45))
        | v4_ordinal1(X45)
        | ~ v3_ordinal1(X45) )
      & ( r2_hidden(esk7_1(X45),X45)
        | v4_ordinal1(X45)
        | ~ v3_ordinal1(X45) )
      & ( ~ r2_hidden(k1_ordinal1(esk7_1(X45)),X45)
        | v4_ordinal1(X45)
        | ~ v3_ordinal1(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_ordinal1])])])])])).

fof(c_0_15,negated_conjecture,(
    ! [X51] :
      ( v3_ordinal1(esk8_0)
      & ( v3_ordinal1(esk9_0)
        | ~ v4_ordinal1(esk8_0) )
      & ( esk8_0 = k1_ordinal1(esk9_0)
        | ~ v4_ordinal1(esk8_0) )
      & ( v4_ordinal1(esk8_0)
        | ~ v4_ordinal1(esk8_0) )
      & ( v3_ordinal1(esk9_0)
        | ~ v3_ordinal1(X51)
        | esk8_0 != k1_ordinal1(X51) )
      & ( esk8_0 = k1_ordinal1(esk9_0)
        | ~ v3_ordinal1(X51)
        | esk8_0 != k1_ordinal1(X51) )
      & ( v4_ordinal1(esk8_0)
        | ~ v3_ordinal1(X51)
        | esk8_0 != k1_ordinal1(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])])).

fof(c_0_16,plain,(
    ! [X38] :
      ( ~ v3_ordinal1(X38)
      | v3_ordinal1(k1_ordinal1(X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

fof(c_0_17,plain,(
    ! [X26] : k1_ordinal1(X26) = k2_xboole_0(X26,k1_tarski(X26)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

cnf(c_0_18,plain,
    ( r2_hidden(esk7_1(X1),X1)
    | v4_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v3_ordinal1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X48,X49] :
      ( ~ r2_hidden(X48,X49)
      | ~ r1_tarski(X49,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_21,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_22,plain,(
    ! [X33] : r2_hidden(X33,k1_ordinal1(X33)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_23,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v3_ordinal1(esk9_0)
    | ~ v4_ordinal1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( v4_ordinal1(esk8_0)
    | r2_hidden(esk7_1(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( esk8_0 = k1_ordinal1(esk9_0)
    | ~ v4_ordinal1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_31,plain,(
    ! [X41,X42] :
      ( ( ~ r2_hidden(X41,k1_ordinal1(X42))
        | r1_ordinal1(X41,X42)
        | ~ v3_ordinal1(X42)
        | ~ v3_ordinal1(X41) )
      & ( ~ r1_ordinal1(X41,X42)
        | r2_hidden(X41,k1_ordinal1(X42))
        | ~ v3_ordinal1(X42)
        | ~ v3_ordinal1(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).

fof(c_0_32,plain,(
    ! [X34,X35] :
      ( ~ v3_ordinal1(X35)
      | ~ r2_hidden(X34,X35)
      | v3_ordinal1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

cnf(c_0_33,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( v3_ordinal1(esk9_0)
    | r2_hidden(esk7_1(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( esk8_0 = k2_xboole_0(esk9_0,k1_tarski(esk9_0))
    | ~ v4_ordinal1(esk8_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_24])).

cnf(c_0_38,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r2_hidden(X1,k1_ordinal1(X2))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk9_0,k1_tarski(esk9_0)))
    | r2_hidden(esk7_1(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_41,plain,(
    ! [X27,X28] :
      ( ( ~ r1_ordinal1(X27,X28)
        | r1_tarski(X27,X28)
        | ~ v3_ordinal1(X27)
        | ~ v3_ordinal1(X28) )
      & ( ~ r1_tarski(X27,X28)
        | r1_ordinal1(X27,X28)
        | ~ v3_ordinal1(X27)
        | ~ v3_ordinal1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_2(k2_xboole_0(X1,k1_tarski(X1)),X1),k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k2_xboole_0(esk9_0,k1_tarski(esk9_0)) = esk8_0
    | r2_hidden(esk7_1(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_26])).

cnf(c_0_44,plain,
    ( r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_38,c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( v3_ordinal1(X1)
    | r2_hidden(esk7_1(esk8_0),esk8_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( r2_hidden(k1_ordinal1(X2),X1)
    | ~ v4_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_19])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,esk9_0),esk8_0)
    | r2_hidden(esk7_1(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( r1_ordinal1(X1,esk9_0)
    | r2_hidden(esk7_1(esk8_0),esk8_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_34])).

cnf(c_0_51,negated_conjecture,
    ( v3_ordinal1(esk1_2(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk9_0))
    | r2_hidden(esk7_1(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_42])).

cnf(c_0_52,plain,
    ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X1)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ v4_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_46,c_0_24])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk7_1(esk8_0),esk8_0)
    | r1_tarski(X1,esk9_0)
    | ~ r1_ordinal1(X1,esk9_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_34])).

cnf(c_0_54,negated_conjecture,
    ( v3_ordinal1(esk1_2(esk8_0,esk9_0))
    | r2_hidden(esk7_1(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( r1_ordinal1(esk1_2(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk9_0),esk9_0)
    | r2_hidden(esk7_1(esk8_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_42])])).

cnf(c_0_56,plain,
    ( r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v4_ordinal1(X2)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_52,c_0_39])).

fof(c_0_57,plain,(
    ! [X36,X37] :
      ( ~ v3_ordinal1(X36)
      | ~ v3_ordinal1(X37)
      | r2_hidden(X36,X37)
      | X36 = X37
      | r2_hidden(X37,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk7_1(esk8_0),esk8_0)
    | r1_tarski(esk1_2(esk8_0,esk9_0),esk9_0)
    | ~ r1_ordinal1(esk1_2(esk8_0,esk9_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r1_ordinal1(esk1_2(esk8_0,esk9_0),esk9_0)
    | r2_hidden(esk7_1(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_43])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk8_0)
    | ~ v4_ordinal1(esk8_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_19])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk7_1(esk8_0),esk8_0)
    | r1_tarski(esk1_2(esk8_0,esk9_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

fof(c_0_63,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk8_0)
    | r2_hidden(esk7_1(esk8_0),esk8_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_26])).

cnf(c_0_65,negated_conjecture,
    ( X1 = esk9_0
    | r2_hidden(esk7_1(esk8_0),esk8_0)
    | r2_hidden(X1,esk9_0)
    | r2_hidden(esk9_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_34])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk7_1(esk8_0),esk8_0)
    | ~ r2_hidden(esk9_0,esk1_2(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_62])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk1_2(esk8_0,esk9_0),k1_tarski(esk1_2(esk8_0,esk9_0))),esk8_0)
    | r2_hidden(esk7_1(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_49])).

cnf(c_0_69,negated_conjecture,
    ( esk1_2(esk8_0,esk9_0) = esk9_0
    | r2_hidden(esk1_2(esk8_0,esk9_0),esk9_0)
    | r2_hidden(esk7_1(esk8_0),esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_54]),c_0_66])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)
    | r2_hidden(esk1_2(esk8_0,esk9_0),esk9_0)
    | r2_hidden(esk7_1(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_70])).

fof(c_0_73,plain,(
    ! [X39,X40] :
      ( ( ~ r2_hidden(X39,X40)
        | r1_ordinal1(k1_ordinal1(X39),X40)
        | ~ v3_ordinal1(X40)
        | ~ v3_ordinal1(X39) )
      & ( ~ r1_ordinal1(k1_ordinal1(X39),X40)
        | r2_hidden(X39,X40)
        | ~ v3_ordinal1(X40)
        | ~ v3_ordinal1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,esk9_0),esk9_0)
    | r2_hidden(esk7_1(esk8_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_43]),c_0_72])).

cnf(c_0_76,plain,
    ( r1_ordinal1(k1_ordinal1(X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk7_1(esk8_0),esk8_0)
    | r1_tarski(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk7_1(esk8_0),esk8_0)
    | r2_hidden(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_43])).

cnf(c_0_79,plain,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_76,c_0_24])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk7_1(esk8_0),esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_77]),c_0_78])).

cnf(c_0_81,plain,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_79,c_0_39])).

cnf(c_0_82,negated_conjecture,
    ( v3_ordinal1(esk7_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),esk8_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_19])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(X1,esk8_0)
    | ~ r1_ordinal1(X1,esk8_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_19])).

cnf(c_0_85,negated_conjecture,
    ( v3_ordinal1(k2_xboole_0(esk7_1(esk8_0),k1_tarski(esk7_1(esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( r1_ordinal1(k2_xboole_0(esk7_1(esk8_0),k1_tarski(esk7_1(esk8_0))),esk8_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk7_1(esk8_0),k1_tarski(esk7_1(esk8_0))),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])])).

cnf(c_0_88,plain,
    ( v4_ordinal1(X1)
    | ~ r2_hidden(k1_ordinal1(esk7_1(X1)),X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_89,negated_conjecture,
    ( v4_ordinal1(esk8_0)
    | ~ v3_ordinal1(X1)
    | esk8_0 != k1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_90,negated_conjecture,
    ( X1 = esk8_0
    | r2_hidden(X1,esk8_0)
    | r2_hidden(esk8_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_19])).

cnf(c_0_91,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k2_xboole_0(esk7_1(esk8_0),k1_tarski(esk7_1(esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_87])).

cnf(c_0_92,plain,
    ( v4_ordinal1(X1)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(k2_xboole_0(esk7_1(X1),k1_tarski(esk7_1(X1))),X1) ),
    inference(rw,[status(thm)],[c_0_88,c_0_24])).

cnf(c_0_93,negated_conjecture,
    ( v4_ordinal1(esk8_0)
    | esk8_0 != k2_xboole_0(X1,k1_tarski(X1))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_89,c_0_24])).

cnf(c_0_94,negated_conjecture,
    ( k2_xboole_0(esk7_1(esk8_0),k1_tarski(esk7_1(esk8_0))) = esk8_0
    | r2_hidden(k2_xboole_0(esk7_1(esk8_0),k1_tarski(esk7_1(esk8_0))),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_85]),c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( v4_ordinal1(esk8_0)
    | ~ r2_hidden(k2_xboole_0(esk7_1(esk8_0),k1_tarski(esk7_1(esk8_0))),esk8_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_19])).

cnf(c_0_96,negated_conjecture,
    ( v4_ordinal1(esk8_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_82])]),c_0_95])).

cnf(c_0_97,negated_conjecture,
    ( k2_xboole_0(esk9_0,k1_tarski(esk9_0)) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_96])])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk8_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_96])])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_97])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_97]),c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:18:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 47.54/47.71  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 47.54/47.71  # and selection function SelectCQIArEqFirst.
% 47.54/47.71  #
% 47.54/47.71  # Preprocessing time       : 0.044 s
% 47.54/47.71  # Presaturation interreduction done
% 47.54/47.71  
% 47.54/47.71  # Proof found!
% 47.54/47.71  # SZS status Theorem
% 47.54/47.71  # SZS output start CNFRefutation
% 47.54/47.71  fof(t42_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>(~((~(v4_ordinal1(X1))&![X2]:(v3_ordinal1(X2)=>X1!=k1_ordinal1(X2))))&~((?[X2]:(v3_ordinal1(X2)&X1=k1_ordinal1(X2))&v4_ordinal1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_ordinal1)).
% 47.54/47.71  fof(t41_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_ordinal1)).
% 47.54/47.71  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 47.54/47.71  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 47.54/47.71  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 47.54/47.71  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 47.54/47.71  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 47.54/47.71  fof(t34_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 47.54/47.71  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 47.54/47.71  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 47.54/47.71  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 47.54/47.71  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 47.54/47.71  fof(t33_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 47.54/47.71  fof(c_0_13, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>(~((~(v4_ordinal1(X1))&![X2]:(v3_ordinal1(X2)=>X1!=k1_ordinal1(X2))))&~((?[X2]:(v3_ordinal1(X2)&X1=k1_ordinal1(X2))&v4_ordinal1(X1)))))), inference(assume_negation,[status(cth)],[t42_ordinal1])).
% 47.54/47.71  fof(c_0_14, plain, ![X45, X46]:((~v4_ordinal1(X45)|(~v3_ordinal1(X46)|(~r2_hidden(X46,X45)|r2_hidden(k1_ordinal1(X46),X45)))|~v3_ordinal1(X45))&((v3_ordinal1(esk7_1(X45))|v4_ordinal1(X45)|~v3_ordinal1(X45))&((r2_hidden(esk7_1(X45),X45)|v4_ordinal1(X45)|~v3_ordinal1(X45))&(~r2_hidden(k1_ordinal1(esk7_1(X45)),X45)|v4_ordinal1(X45)|~v3_ordinal1(X45))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_ordinal1])])])])])).
% 47.54/47.71  fof(c_0_15, negated_conjecture, ![X51]:(v3_ordinal1(esk8_0)&((((v3_ordinal1(esk9_0)|~v4_ordinal1(esk8_0))&(esk8_0=k1_ordinal1(esk9_0)|~v4_ordinal1(esk8_0)))&(v4_ordinal1(esk8_0)|~v4_ordinal1(esk8_0)))&(((v3_ordinal1(esk9_0)|(~v3_ordinal1(X51)|esk8_0!=k1_ordinal1(X51)))&(esk8_0=k1_ordinal1(esk9_0)|(~v3_ordinal1(X51)|esk8_0!=k1_ordinal1(X51))))&(v4_ordinal1(esk8_0)|(~v3_ordinal1(X51)|esk8_0!=k1_ordinal1(X51)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])])).
% 47.54/47.71  fof(c_0_16, plain, ![X38]:(~v3_ordinal1(X38)|v3_ordinal1(k1_ordinal1(X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 47.54/47.71  fof(c_0_17, plain, ![X26]:k1_ordinal1(X26)=k2_xboole_0(X26,k1_tarski(X26)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 47.54/47.71  cnf(c_0_18, plain, (r2_hidden(esk7_1(X1),X1)|v4_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 47.54/47.71  cnf(c_0_19, negated_conjecture, (v3_ordinal1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 47.54/47.71  fof(c_0_20, plain, ![X48, X49]:(~r2_hidden(X48,X49)|~r1_tarski(X49,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 47.54/47.71  fof(c_0_21, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 47.54/47.71  fof(c_0_22, plain, ![X33]:r2_hidden(X33,k1_ordinal1(X33)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 47.54/47.71  cnf(c_0_23, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 47.54/47.71  cnf(c_0_24, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 47.54/47.71  cnf(c_0_25, negated_conjecture, (v3_ordinal1(esk9_0)|~v4_ordinal1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 47.54/47.71  cnf(c_0_26, negated_conjecture, (v4_ordinal1(esk8_0)|r2_hidden(esk7_1(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 47.54/47.71  cnf(c_0_27, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 47.54/47.71  cnf(c_0_28, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 47.54/47.71  cnf(c_0_29, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 47.54/47.71  cnf(c_0_30, negated_conjecture, (esk8_0=k1_ordinal1(esk9_0)|~v4_ordinal1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 47.54/47.71  fof(c_0_31, plain, ![X41, X42]:((~r2_hidden(X41,k1_ordinal1(X42))|r1_ordinal1(X41,X42)|~v3_ordinal1(X42)|~v3_ordinal1(X41))&(~r1_ordinal1(X41,X42)|r2_hidden(X41,k1_ordinal1(X42))|~v3_ordinal1(X42)|~v3_ordinal1(X41))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).
% 47.54/47.71  fof(c_0_32, plain, ![X34, X35]:(~v3_ordinal1(X35)|(~r2_hidden(X34,X35)|v3_ordinal1(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 47.54/47.71  cnf(c_0_33, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 47.54/47.71  cnf(c_0_34, negated_conjecture, (v3_ordinal1(esk9_0)|r2_hidden(esk7_1(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 47.54/47.71  cnf(c_0_35, plain, (r2_hidden(esk1_2(X1,X2),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 47.54/47.71  cnf(c_0_36, plain, (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_29, c_0_24])).
% 47.54/47.71  cnf(c_0_37, negated_conjecture, (esk8_0=k2_xboole_0(esk9_0,k1_tarski(esk9_0))|~v4_ordinal1(esk8_0)), inference(rw,[status(thm)],[c_0_30, c_0_24])).
% 47.54/47.71  cnf(c_0_38, plain, (r1_ordinal1(X1,X2)|~r2_hidden(X1,k1_ordinal1(X2))|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 47.54/47.71  cnf(c_0_39, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 47.54/47.71  cnf(c_0_40, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk9_0,k1_tarski(esk9_0)))|r2_hidden(esk7_1(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 47.54/47.71  fof(c_0_41, plain, ![X27, X28]:((~r1_ordinal1(X27,X28)|r1_tarski(X27,X28)|(~v3_ordinal1(X27)|~v3_ordinal1(X28)))&(~r1_tarski(X27,X28)|r1_ordinal1(X27,X28)|(~v3_ordinal1(X27)|~v3_ordinal1(X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 47.54/47.71  cnf(c_0_42, plain, (r2_hidden(esk1_2(k2_xboole_0(X1,k1_tarski(X1)),X1),k2_xboole_0(X1,k1_tarski(X1)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 47.54/47.71  cnf(c_0_43, negated_conjecture, (k2_xboole_0(esk9_0,k1_tarski(esk9_0))=esk8_0|r2_hidden(esk7_1(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_37, c_0_26])).
% 47.54/47.71  cnf(c_0_44, plain, (r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_38, c_0_24])).
% 47.54/47.71  cnf(c_0_45, negated_conjecture, (v3_ordinal1(X1)|r2_hidden(esk7_1(esk8_0),esk8_0)|~r2_hidden(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0)))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 47.54/47.71  cnf(c_0_46, plain, (r2_hidden(k1_ordinal1(X2),X1)|~v4_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X2,X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 47.54/47.71  cnf(c_0_47, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 47.54/47.71  cnf(c_0_48, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_39, c_0_19])).
% 47.54/47.71  cnf(c_0_49, negated_conjecture, (r2_hidden(esk1_2(esk8_0,esk9_0),esk8_0)|r2_hidden(esk7_1(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 47.54/47.71  cnf(c_0_50, negated_conjecture, (r1_ordinal1(X1,esk9_0)|r2_hidden(esk7_1(esk8_0),esk8_0)|~v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(esk9_0,k1_tarski(esk9_0)))), inference(spm,[status(thm)],[c_0_44, c_0_34])).
% 47.54/47.71  cnf(c_0_51, negated_conjecture, (v3_ordinal1(esk1_2(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk9_0))|r2_hidden(esk7_1(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_45, c_0_42])).
% 47.54/47.71  cnf(c_0_52, plain, (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X1)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~v4_ordinal1(X1)|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_46, c_0_24])).
% 47.54/47.71  cnf(c_0_53, negated_conjecture, (r2_hidden(esk7_1(esk8_0),esk8_0)|r1_tarski(X1,esk9_0)|~r1_ordinal1(X1,esk9_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_34])).
% 47.54/47.71  cnf(c_0_54, negated_conjecture, (v3_ordinal1(esk1_2(esk8_0,esk9_0))|r2_hidden(esk7_1(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 47.54/47.71  cnf(c_0_55, negated_conjecture, (r1_ordinal1(esk1_2(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk9_0),esk9_0)|r2_hidden(esk7_1(esk8_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_42])])).
% 47.54/47.71  cnf(c_0_56, plain, (r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v4_ordinal1(X2)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_52, c_0_39])).
% 47.54/47.71  fof(c_0_57, plain, ![X36, X37]:(~v3_ordinal1(X36)|(~v3_ordinal1(X37)|(r2_hidden(X36,X37)|X36=X37|r2_hidden(X37,X36)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 47.54/47.71  cnf(c_0_58, negated_conjecture, (r2_hidden(esk7_1(esk8_0),esk8_0)|r1_tarski(esk1_2(esk8_0,esk9_0),esk9_0)|~r1_ordinal1(esk1_2(esk8_0,esk9_0),esk9_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 47.54/47.71  cnf(c_0_59, negated_conjecture, (r1_ordinal1(esk1_2(esk8_0,esk9_0),esk9_0)|r2_hidden(esk7_1(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_55, c_0_43])).
% 47.54/47.71  cnf(c_0_60, negated_conjecture, (r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk8_0)|~v4_ordinal1(esk8_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_56, c_0_19])).
% 47.54/47.71  cnf(c_0_61, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 47.54/47.71  cnf(c_0_62, negated_conjecture, (r2_hidden(esk7_1(esk8_0),esk8_0)|r1_tarski(esk1_2(esk8_0,esk9_0),esk9_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 47.54/47.71  fof(c_0_63, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 47.54/47.71  cnf(c_0_64, negated_conjecture, (r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk8_0)|r2_hidden(esk7_1(esk8_0),esk8_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_60, c_0_26])).
% 47.54/47.71  cnf(c_0_65, negated_conjecture, (X1=esk9_0|r2_hidden(esk7_1(esk8_0),esk8_0)|r2_hidden(X1,esk9_0)|r2_hidden(esk9_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_61, c_0_34])).
% 47.54/47.71  cnf(c_0_66, negated_conjecture, (r2_hidden(esk7_1(esk8_0),esk8_0)|~r2_hidden(esk9_0,esk1_2(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_27, c_0_62])).
% 47.54/47.71  cnf(c_0_67, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_63])).
% 47.54/47.71  cnf(c_0_68, negated_conjecture, (r2_hidden(k2_xboole_0(esk1_2(esk8_0,esk9_0),k1_tarski(esk1_2(esk8_0,esk9_0))),esk8_0)|r2_hidden(esk7_1(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_64, c_0_49])).
% 47.54/47.71  cnf(c_0_69, negated_conjecture, (esk1_2(esk8_0,esk9_0)=esk9_0|r2_hidden(esk1_2(esk8_0,esk9_0),esk9_0)|r2_hidden(esk7_1(esk8_0),esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_54]), c_0_66])).
% 47.54/47.71  cnf(c_0_70, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_67])).
% 47.54/47.71  cnf(c_0_71, negated_conjecture, (r2_hidden(k2_xboole_0(esk9_0,k1_tarski(esk9_0)),esk8_0)|r2_hidden(esk1_2(esk8_0,esk9_0),esk9_0)|r2_hidden(esk7_1(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 47.54/47.71  cnf(c_0_72, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_27, c_0_70])).
% 47.54/47.71  fof(c_0_73, plain, ![X39, X40]:((~r2_hidden(X39,X40)|r1_ordinal1(k1_ordinal1(X39),X40)|~v3_ordinal1(X40)|~v3_ordinal1(X39))&(~r1_ordinal1(k1_ordinal1(X39),X40)|r2_hidden(X39,X40)|~v3_ordinal1(X40)|~v3_ordinal1(X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_ordinal1])])])])).
% 47.54/47.71  cnf(c_0_74, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 47.54/47.71  cnf(c_0_75, negated_conjecture, (r2_hidden(esk1_2(esk8_0,esk9_0),esk9_0)|r2_hidden(esk7_1(esk8_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_43]), c_0_72])).
% 47.54/47.71  cnf(c_0_76, plain, (r1_ordinal1(k1_ordinal1(X1),X2)|~r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 47.54/47.71  cnf(c_0_77, negated_conjecture, (r2_hidden(esk7_1(esk8_0),esk8_0)|r1_tarski(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 47.54/47.71  cnf(c_0_78, negated_conjecture, (r2_hidden(esk7_1(esk8_0),esk8_0)|r2_hidden(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_36, c_0_43])).
% 47.54/47.71  cnf(c_0_79, plain, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_76, c_0_24])).
% 47.54/47.71  cnf(c_0_80, negated_conjecture, (r2_hidden(esk7_1(esk8_0),esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_77]), c_0_78])).
% 47.54/47.71  cnf(c_0_81, plain, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),X2)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_79, c_0_39])).
% 47.54/47.71  cnf(c_0_82, negated_conjecture, (v3_ordinal1(esk7_1(esk8_0))), inference(spm,[status(thm)],[c_0_48, c_0_80])).
% 47.54/47.71  cnf(c_0_83, negated_conjecture, (r1_ordinal1(k2_xboole_0(X1,k1_tarski(X1)),esk8_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_81, c_0_19])).
% 47.54/47.71  cnf(c_0_84, negated_conjecture, (r1_tarski(X1,esk8_0)|~r1_ordinal1(X1,esk8_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_19])).
% 47.54/47.71  cnf(c_0_85, negated_conjecture, (v3_ordinal1(k2_xboole_0(esk7_1(esk8_0),k1_tarski(esk7_1(esk8_0))))), inference(spm,[status(thm)],[c_0_33, c_0_82])).
% 47.54/47.71  cnf(c_0_86, negated_conjecture, (r1_ordinal1(k2_xboole_0(esk7_1(esk8_0),k1_tarski(esk7_1(esk8_0))),esk8_0)), inference(spm,[status(thm)],[c_0_83, c_0_80])).
% 47.54/47.71  cnf(c_0_87, negated_conjecture, (r1_tarski(k2_xboole_0(esk7_1(esk8_0),k1_tarski(esk7_1(esk8_0))),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])])).
% 47.54/47.71  cnf(c_0_88, plain, (v4_ordinal1(X1)|~r2_hidden(k1_ordinal1(esk7_1(X1)),X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 47.54/47.72  cnf(c_0_89, negated_conjecture, (v4_ordinal1(esk8_0)|~v3_ordinal1(X1)|esk8_0!=k1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 47.54/47.72  cnf(c_0_90, negated_conjecture, (X1=esk8_0|r2_hidden(X1,esk8_0)|r2_hidden(esk8_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_61, c_0_19])).
% 47.54/47.72  cnf(c_0_91, negated_conjecture, (~r2_hidden(esk8_0,k2_xboole_0(esk7_1(esk8_0),k1_tarski(esk7_1(esk8_0))))), inference(spm,[status(thm)],[c_0_27, c_0_87])).
% 47.54/47.72  cnf(c_0_92, plain, (v4_ordinal1(X1)|~v3_ordinal1(X1)|~r2_hidden(k2_xboole_0(esk7_1(X1),k1_tarski(esk7_1(X1))),X1)), inference(rw,[status(thm)],[c_0_88, c_0_24])).
% 47.54/47.72  cnf(c_0_93, negated_conjecture, (v4_ordinal1(esk8_0)|esk8_0!=k2_xboole_0(X1,k1_tarski(X1))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_89, c_0_24])).
% 47.54/47.72  cnf(c_0_94, negated_conjecture, (k2_xboole_0(esk7_1(esk8_0),k1_tarski(esk7_1(esk8_0)))=esk8_0|r2_hidden(k2_xboole_0(esk7_1(esk8_0),k1_tarski(esk7_1(esk8_0))),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_85]), c_0_91])).
% 47.54/47.72  cnf(c_0_95, negated_conjecture, (v4_ordinal1(esk8_0)|~r2_hidden(k2_xboole_0(esk7_1(esk8_0),k1_tarski(esk7_1(esk8_0))),esk8_0)), inference(spm,[status(thm)],[c_0_92, c_0_19])).
% 47.54/47.72  cnf(c_0_96, negated_conjecture, (v4_ordinal1(esk8_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_82])]), c_0_95])).
% 47.54/47.72  cnf(c_0_97, negated_conjecture, (k2_xboole_0(esk9_0,k1_tarski(esk9_0))=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_96])])).
% 47.54/47.72  cnf(c_0_98, negated_conjecture, (r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),esk8_0)|~r2_hidden(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_96])])).
% 47.54/47.72  cnf(c_0_99, negated_conjecture, (r2_hidden(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_36, c_0_97])).
% 47.54/47.72  cnf(c_0_100, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_97]), c_0_72]), ['proof']).
% 47.54/47.72  # SZS output end CNFRefutation
% 47.54/47.72  # Proof object total steps             : 101
% 47.54/47.72  # Proof object clause steps            : 74
% 47.54/47.72  # Proof object formula steps           : 27
% 47.54/47.72  # Proof object conjectures             : 50
% 47.54/47.72  # Proof object clause conjectures      : 47
% 47.54/47.72  # Proof object formula conjectures     : 3
% 47.54/47.72  # Proof object initial clauses used    : 19
% 47.54/47.72  # Proof object initial formulas used   : 13
% 47.54/47.72  # Proof object generating inferences   : 42
% 47.54/47.72  # Proof object simplifying inferences  : 28
% 47.54/47.72  # Training examples: 0 positive, 0 negative
% 47.54/47.72  # Parsed axioms                        : 17
% 47.54/47.72  # Removed by relevancy pruning/SinE    : 0
% 47.54/47.72  # Initial clauses                      : 41
% 47.54/47.72  # Removed in clause preprocessing      : 2
% 47.54/47.72  # Initial clauses in saturation        : 39
% 47.54/47.72  # Processed clauses                    : 33446
% 47.54/47.72  # ...of these trivial                  : 1111
% 47.54/47.72  # ...subsumed                          : 14473
% 47.54/47.72  # ...remaining for further processing  : 17862
% 47.54/47.72  # Other redundant clauses eliminated   : 903
% 47.54/47.72  # Clauses deleted for lack of memory   : 536797
% 47.54/47.72  # Backward-subsumed                    : 1672
% 47.54/47.72  # Backward-rewritten                   : 3306
% 47.54/47.72  # Generated clauses                    : 3949684
% 47.54/47.72  # ...of the previous two non-trivial   : 3483828
% 47.54/47.72  # Contextual simplify-reflections      : 301
% 47.54/47.72  # Paramodulations                      : 3948568
% 47.54/47.72  # Factorizations                       : 196
% 47.54/47.72  # Equation resolutions                 : 903
% 47.54/47.72  # Propositional unsat checks           : 0
% 47.54/47.72  #    Propositional check models        : 0
% 47.54/47.72  #    Propositional check unsatisfiable : 0
% 47.54/47.72  #    Propositional clauses             : 0
% 47.54/47.72  #    Propositional clauses after purity: 0
% 47.54/47.72  #    Propositional unsat core size     : 0
% 47.54/47.72  #    Propositional preprocessing time  : 0.000
% 47.54/47.72  #    Propositional encoding time       : 0.000
% 47.54/47.72  #    Propositional solver time         : 0.000
% 47.54/47.72  #    Success case prop preproc time    : 0.000
% 47.54/47.72  #    Success case prop encoding time   : 0.000
% 47.54/47.72  #    Success case prop solver time     : 0.000
% 47.54/47.72  # Current number of processed clauses  : 12824
% 47.54/47.72  #    Positive orientable unit clauses  : 2713
% 47.54/47.72  #    Positive unorientable unit clauses: 0
% 47.54/47.72  #    Negative unit clauses             : 326
% 47.54/47.72  #    Non-unit-clauses                  : 9785
% 47.54/47.72  # Current number of unprocessed clauses: 1174985
% 47.54/47.72  # ...number of literals in the above   : 4729127
% 47.54/47.72  # Current number of archived formulas  : 0
% 47.54/47.72  # Current number of archived clauses   : 5034
% 47.54/47.72  # Clause-clause subsumption calls (NU) : 16318082
% 47.54/47.72  # Rec. Clause-clause subsumption calls : 7623493
% 47.54/47.72  # Non-unit clause-clause subsumptions  : 12936
% 47.54/47.72  # Unit Clause-clause subsumption calls : 4227578
% 47.54/47.72  # Rewrite failures with RHS unbound    : 0
% 47.54/47.72  # BW rewrite match attempts            : 37498
% 47.54/47.72  # BW rewrite match successes           : 201
% 47.54/47.72  # Condensation attempts                : 0
% 47.54/47.72  # Condensation successes               : 0
% 47.54/47.72  # Termbank termtop insertions          : 124220948
% 47.57/47.81  
% 47.57/47.81  # -------------------------------------------------
% 47.57/47.81  # User time                : 46.422 s
% 47.57/47.81  # System time              : 1.057 s
% 47.57/47.81  # Total time               : 47.478 s
% 47.57/47.81  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
