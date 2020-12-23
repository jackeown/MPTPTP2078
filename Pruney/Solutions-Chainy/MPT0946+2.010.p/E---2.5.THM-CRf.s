%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:43 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 678 expanded)
%              Number of clauses        :   38 ( 277 expanded)
%              Number of leaves         :   13 ( 176 expanded)
%              Depth                    :   12
%              Number of atoms          :  310 (2941 expanded)
%              Number of equality atoms :   63 ( 683 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   51 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d1_wellord2,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k1_wellord2(X1)
      <=> ( k3_relat_1(X2) = X1
          & ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1) )
             => ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r1_tarski(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(t36_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( ( v2_wellord1(X2)
          & r1_tarski(X1,k3_relat_1(X2)) )
       => ( ~ ( X1 != k3_relat_1(X2)
              & ! [X3] :
                  ~ ( r2_hidden(X3,k3_relat_1(X2))
                    & X1 = k1_wellord1(X2,X3) ) )
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
             => ! [X4] :
                  ( r2_hidden(k4_tarski(X4,X3),X2)
                 => r2_hidden(X4,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_wellord1)).

fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(t57_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(t10_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
           => X1 = k1_wellord1(k1_wellord2(X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

fof(t7_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v2_wellord1(k1_wellord2(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

fof(t11_wellord2,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

fof(t8_wellord2,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(t50_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r4_wellord1(X1,X2)
           => r4_wellord1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_13,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_14,plain,(
    ! [X35,X36,X37,X38] :
      ( ( k3_relat_1(X36) = X35
        | X36 != k1_wellord2(X35)
        | ~ v1_relat_1(X36) )
      & ( ~ r2_hidden(k4_tarski(X37,X38),X36)
        | r1_tarski(X37,X38)
        | ~ r2_hidden(X37,X35)
        | ~ r2_hidden(X38,X35)
        | X36 != k1_wellord2(X35)
        | ~ v1_relat_1(X36) )
      & ( ~ r1_tarski(X37,X38)
        | r2_hidden(k4_tarski(X37,X38),X36)
        | ~ r2_hidden(X37,X35)
        | ~ r2_hidden(X38,X35)
        | X36 != k1_wellord2(X35)
        | ~ v1_relat_1(X36) )
      & ( r2_hidden(esk6_2(X35,X36),X35)
        | k3_relat_1(X36) != X35
        | X36 = k1_wellord2(X35)
        | ~ v1_relat_1(X36) )
      & ( r2_hidden(esk7_2(X35,X36),X35)
        | k3_relat_1(X36) != X35
        | X36 = k1_wellord2(X35)
        | ~ v1_relat_1(X36) )
      & ( ~ r2_hidden(k4_tarski(esk6_2(X35,X36),esk7_2(X35,X36)),X36)
        | ~ r1_tarski(esk6_2(X35,X36),esk7_2(X35,X36))
        | k3_relat_1(X36) != X35
        | X36 = k1_wellord2(X35)
        | ~ v1_relat_1(X36) )
      & ( r2_hidden(k4_tarski(esk6_2(X35,X36),esk7_2(X35,X36)),X36)
        | r1_tarski(esk6_2(X35,X36),esk7_2(X35,X36))
        | k3_relat_1(X36) != X35
        | X36 = k1_wellord2(X35)
        | ~ v1_relat_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_15,plain,(
    ! [X41] : v1_relat_1(k1_wellord2(X41)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_16,plain,(
    ! [X23,X24,X25,X26,X27] :
      ( ( X23 != k3_relat_1(X24)
        | ~ r2_hidden(X26,X23)
        | ~ r2_hidden(k4_tarski(X27,X26),X24)
        | r2_hidden(X27,X23)
        | ~ v2_wellord1(X24)
        | ~ r1_tarski(X23,k3_relat_1(X24))
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(X25,k3_relat_1(X24))
        | X23 != k1_wellord1(X24,X25)
        | ~ r2_hidden(X26,X23)
        | ~ r2_hidden(k4_tarski(X27,X26),X24)
        | r2_hidden(X27,X23)
        | ~ v2_wellord1(X24)
        | ~ r1_tarski(X23,k3_relat_1(X24))
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(esk5_2(X23,X24),k3_relat_1(X24))
        | X23 = k3_relat_1(X24)
        | r2_hidden(esk3_2(X23,X24),X23)
        | ~ v2_wellord1(X24)
        | ~ r1_tarski(X23,k3_relat_1(X24))
        | ~ v1_relat_1(X24) )
      & ( X23 = k1_wellord1(X24,esk5_2(X23,X24))
        | X23 = k3_relat_1(X24)
        | r2_hidden(esk3_2(X23,X24),X23)
        | ~ v2_wellord1(X24)
        | ~ r1_tarski(X23,k3_relat_1(X24))
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(esk5_2(X23,X24),k3_relat_1(X24))
        | X23 = k3_relat_1(X24)
        | r2_hidden(k4_tarski(esk4_2(X23,X24),esk3_2(X23,X24)),X24)
        | ~ v2_wellord1(X24)
        | ~ r1_tarski(X23,k3_relat_1(X24))
        | ~ v1_relat_1(X24) )
      & ( X23 = k1_wellord1(X24,esk5_2(X23,X24))
        | X23 = k3_relat_1(X24)
        | r2_hidden(k4_tarski(esk4_2(X23,X24),esk3_2(X23,X24)),X24)
        | ~ v2_wellord1(X24)
        | ~ r1_tarski(X23,k3_relat_1(X24))
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(esk5_2(X23,X24),k3_relat_1(X24))
        | X23 = k3_relat_1(X24)
        | ~ r2_hidden(esk4_2(X23,X24),X23)
        | ~ v2_wellord1(X24)
        | ~ r1_tarski(X23,k3_relat_1(X24))
        | ~ v1_relat_1(X24) )
      & ( X23 = k1_wellord1(X24,esk5_2(X23,X24))
        | X23 = k3_relat_1(X24)
        | ~ r2_hidden(esk4_2(X23,X24),X23)
        | ~ v2_wellord1(X24)
        | ~ r1_tarski(X23,k3_relat_1(X24))
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_wellord1])])])])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21] :
      ( ( X18 != X16
        | ~ r2_hidden(X18,X17)
        | X17 != k1_wellord1(X15,X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(X18,X16),X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k1_wellord1(X15,X16)
        | ~ v1_relat_1(X15) )
      & ( X19 = X16
        | ~ r2_hidden(k4_tarski(X19,X16),X15)
        | r2_hidden(X19,X17)
        | X17 != k1_wellord1(X15,X16)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(esk2_3(X15,X20,X21),X21)
        | esk2_3(X15,X20,X21) = X20
        | ~ r2_hidden(k4_tarski(esk2_3(X15,X20,X21),X20),X15)
        | X21 = k1_wellord1(X15,X20)
        | ~ v1_relat_1(X15) )
      & ( esk2_3(X15,X20,X21) != X20
        | r2_hidden(esk2_3(X15,X20,X21),X21)
        | X21 = k1_wellord1(X15,X20)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(esk2_3(X15,X20,X21),X20),X15)
        | r2_hidden(esk2_3(X15,X20,X21),X21)
        | X21 = k1_wellord1(X15,X20)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

fof(c_0_19,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X33)
      | ~ v2_wellord1(X33)
      | ~ r2_hidden(X34,k3_relat_1(X33))
      | ~ r4_wellord1(X33,k2_wellord1(X33,k1_wellord1(X33,X34))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).

fof(c_0_20,plain,(
    ! [X42,X43] :
      ( ~ v3_ordinal1(X42)
      | ~ v3_ordinal1(X43)
      | ~ r2_hidden(X42,X43)
      | X42 = k1_wellord1(k1_wellord2(X43),X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).

cnf(c_0_21,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X44] :
      ( ~ v3_ordinal1(X44)
      | v2_wellord1(k1_wellord2(X44)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
             => X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t11_wellord2])).

cnf(c_0_25,plain,
    ( r2_hidden(X4,X1)
    | X1 != k3_relat_1(X2)
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(k4_tarski(X4,X3),X2)
    | ~ v2_wellord1(X2)
    | ~ r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( X1 = k1_wellord1(k1_wellord2(X2),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_22])])).

cnf(c_0_31,plain,
    ( v2_wellord1(k1_wellord2(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X45,X46] :
      ( ~ r1_tarski(X45,X46)
      | k2_wellord1(k1_wellord2(X46),X45) = k1_wellord2(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).

fof(c_0_33,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X31)
      | ~ v1_relat_1(X32)
      | ~ r4_wellord1(X31,X32)
      | r4_wellord1(X32,X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).

fof(c_0_34,negated_conjecture,
    ( v3_ordinal1(esk8_0)
    & v3_ordinal1(esk9_0)
    & r4_wellord1(k1_wellord2(esk8_0),k1_wellord2(esk9_0))
    & esk8_0 != esk9_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_35,plain,(
    ! [X13,X14] :
      ( ~ v3_ordinal1(X13)
      | ~ v3_ordinal1(X14)
      | r2_hidden(X13,X14)
      | X13 = X14
      | r2_hidden(X14,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X3,k3_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_26])])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k1_wellord1(X3,X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),X2))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X2,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_22])]),c_0_30])]),c_0_31])).

cnf(c_0_39,plain,
    ( k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r4_wellord1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk8_0),k1_wellord2(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( v3_ordinal1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_wellord1(X2,X3))
    | ~ r2_hidden(X3,k3_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_45,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_46,plain,
    ( ~ r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X2,X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk9_0),k1_wellord2(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_22]),c_0_22])])).

cnf(c_0_48,negated_conjecture,
    ( v3_ordinal1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_49,negated_conjecture,
    ( X1 = esk9_0
    | r2_hidden(esk9_0,X1)
    | r2_hidden(X1,esk9_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( esk8_0 != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X3)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_29]),c_0_30]),c_0_22]),c_0_30])]),c_0_31])).

cnf(c_0_52,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(esk8_0,esk9_0)
    | ~ r1_tarski(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_43]),c_0_48])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk8_0,esk9_0)
    | r2_hidden(esk9_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_48]),c_0_50])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ v3_ordinal1(X3)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(esk9_0,esk8_0)
    | ~ r1_tarski(esk9_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_41]),c_0_48]),c_0_43])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0)
    | ~ r1_tarski(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_tarski(esk9_0,esk8_0)
    | ~ r1_tarski(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(esk8_0,esk9_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_58]),c_0_48]),c_0_43])]),c_0_60])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_54]),c_0_43]),c_0_48])]),c_0_61])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tarski(esk9_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_62])])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_62]),c_0_48]),c_0_43])]),c_0_63]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.19/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.029 s
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.38  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.19/0.38  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.19/0.38  fof(t36_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>((v2_wellord1(X2)&r1_tarski(X1,k3_relat_1(X2)))=>(~((X1!=k3_relat_1(X2)&![X3]:~((r2_hidden(X3,k3_relat_1(X2))&X1=k1_wellord1(X2,X3)))))<=>![X3]:(r2_hidden(X3,X1)=>![X4]:(r2_hidden(k4_tarski(X4,X3),X2)=>r2_hidden(X4,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_wellord1)).
% 0.19/0.38  fof(d1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k1_wellord1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4!=X2&r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 0.19/0.38  fof(t57_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)=>![X2]:~((r2_hidden(X2,k3_relat_1(X1))&r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_wellord1)).
% 0.19/0.38  fof(t10_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>X1=k1_wellord1(k1_wellord2(X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_wellord2)).
% 0.19/0.38  fof(t7_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>v2_wellord1(k1_wellord2(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_wellord2)).
% 0.19/0.38  fof(t11_wellord2, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_wellord2)).
% 0.19/0.38  fof(t8_wellord2, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 0.19/0.38  fof(t50_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r4_wellord1(X1,X2)=>r4_wellord1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_wellord1)).
% 0.19/0.38  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 0.19/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.38  fof(c_0_13, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.38  fof(c_0_14, plain, ![X35, X36, X37, X38]:(((k3_relat_1(X36)=X35|X36!=k1_wellord2(X35)|~v1_relat_1(X36))&((~r2_hidden(k4_tarski(X37,X38),X36)|r1_tarski(X37,X38)|(~r2_hidden(X37,X35)|~r2_hidden(X38,X35))|X36!=k1_wellord2(X35)|~v1_relat_1(X36))&(~r1_tarski(X37,X38)|r2_hidden(k4_tarski(X37,X38),X36)|(~r2_hidden(X37,X35)|~r2_hidden(X38,X35))|X36!=k1_wellord2(X35)|~v1_relat_1(X36))))&(((r2_hidden(esk6_2(X35,X36),X35)|k3_relat_1(X36)!=X35|X36=k1_wellord2(X35)|~v1_relat_1(X36))&(r2_hidden(esk7_2(X35,X36),X35)|k3_relat_1(X36)!=X35|X36=k1_wellord2(X35)|~v1_relat_1(X36)))&((~r2_hidden(k4_tarski(esk6_2(X35,X36),esk7_2(X35,X36)),X36)|~r1_tarski(esk6_2(X35,X36),esk7_2(X35,X36))|k3_relat_1(X36)!=X35|X36=k1_wellord2(X35)|~v1_relat_1(X36))&(r2_hidden(k4_tarski(esk6_2(X35,X36),esk7_2(X35,X36)),X36)|r1_tarski(esk6_2(X35,X36),esk7_2(X35,X36))|k3_relat_1(X36)!=X35|X36=k1_wellord2(X35)|~v1_relat_1(X36))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.19/0.38  fof(c_0_15, plain, ![X41]:v1_relat_1(k1_wellord2(X41)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.19/0.38  fof(c_0_16, plain, ![X23, X24, X25, X26, X27]:(((X23!=k3_relat_1(X24)|(~r2_hidden(X26,X23)|(~r2_hidden(k4_tarski(X27,X26),X24)|r2_hidden(X27,X23)))|(~v2_wellord1(X24)|~r1_tarski(X23,k3_relat_1(X24)))|~v1_relat_1(X24))&(~r2_hidden(X25,k3_relat_1(X24))|X23!=k1_wellord1(X24,X25)|(~r2_hidden(X26,X23)|(~r2_hidden(k4_tarski(X27,X26),X24)|r2_hidden(X27,X23)))|(~v2_wellord1(X24)|~r1_tarski(X23,k3_relat_1(X24)))|~v1_relat_1(X24)))&(((r2_hidden(esk5_2(X23,X24),k3_relat_1(X24))|X23=k3_relat_1(X24)|r2_hidden(esk3_2(X23,X24),X23)|(~v2_wellord1(X24)|~r1_tarski(X23,k3_relat_1(X24)))|~v1_relat_1(X24))&(X23=k1_wellord1(X24,esk5_2(X23,X24))|X23=k3_relat_1(X24)|r2_hidden(esk3_2(X23,X24),X23)|(~v2_wellord1(X24)|~r1_tarski(X23,k3_relat_1(X24)))|~v1_relat_1(X24)))&(((r2_hidden(esk5_2(X23,X24),k3_relat_1(X24))|X23=k3_relat_1(X24)|r2_hidden(k4_tarski(esk4_2(X23,X24),esk3_2(X23,X24)),X24)|(~v2_wellord1(X24)|~r1_tarski(X23,k3_relat_1(X24)))|~v1_relat_1(X24))&(X23=k1_wellord1(X24,esk5_2(X23,X24))|X23=k3_relat_1(X24)|r2_hidden(k4_tarski(esk4_2(X23,X24),esk3_2(X23,X24)),X24)|(~v2_wellord1(X24)|~r1_tarski(X23,k3_relat_1(X24)))|~v1_relat_1(X24)))&((r2_hidden(esk5_2(X23,X24),k3_relat_1(X24))|X23=k3_relat_1(X24)|~r2_hidden(esk4_2(X23,X24),X23)|(~v2_wellord1(X24)|~r1_tarski(X23,k3_relat_1(X24)))|~v1_relat_1(X24))&(X23=k1_wellord1(X24,esk5_2(X23,X24))|X23=k3_relat_1(X24)|~r2_hidden(esk4_2(X23,X24),X23)|(~v2_wellord1(X24)|~r1_tarski(X23,k3_relat_1(X24)))|~v1_relat_1(X24)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_wellord1])])])])])).
% 0.19/0.38  cnf(c_0_17, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  fof(c_0_18, plain, ![X15, X16, X17, X18, X19, X20, X21]:((((X18!=X16|~r2_hidden(X18,X17)|X17!=k1_wellord1(X15,X16)|~v1_relat_1(X15))&(r2_hidden(k4_tarski(X18,X16),X15)|~r2_hidden(X18,X17)|X17!=k1_wellord1(X15,X16)|~v1_relat_1(X15)))&(X19=X16|~r2_hidden(k4_tarski(X19,X16),X15)|r2_hidden(X19,X17)|X17!=k1_wellord1(X15,X16)|~v1_relat_1(X15)))&((~r2_hidden(esk2_3(X15,X20,X21),X21)|(esk2_3(X15,X20,X21)=X20|~r2_hidden(k4_tarski(esk2_3(X15,X20,X21),X20),X15))|X21=k1_wellord1(X15,X20)|~v1_relat_1(X15))&((esk2_3(X15,X20,X21)!=X20|r2_hidden(esk2_3(X15,X20,X21),X21)|X21=k1_wellord1(X15,X20)|~v1_relat_1(X15))&(r2_hidden(k4_tarski(esk2_3(X15,X20,X21),X20),X15)|r2_hidden(esk2_3(X15,X20,X21),X21)|X21=k1_wellord1(X15,X20)|~v1_relat_1(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).
% 0.19/0.38  fof(c_0_19, plain, ![X33, X34]:(~v1_relat_1(X33)|(~v2_wellord1(X33)|(~r2_hidden(X34,k3_relat_1(X33))|~r4_wellord1(X33,k2_wellord1(X33,k1_wellord1(X33,X34)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).
% 0.19/0.38  fof(c_0_20, plain, ![X42, X43]:(~v3_ordinal1(X42)|(~v3_ordinal1(X43)|(~r2_hidden(X42,X43)|X42=k1_wellord1(k1_wellord2(X43),X42)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).
% 0.19/0.38  cnf(c_0_21, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_22, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  fof(c_0_23, plain, ![X44]:(~v3_ordinal1(X44)|v2_wellord1(k1_wellord2(X44))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).
% 0.19/0.38  fof(c_0_24, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2)))), inference(assume_negation,[status(cth)],[t11_wellord2])).
% 0.19/0.38  cnf(c_0_25, plain, (r2_hidden(X4,X1)|X1!=k3_relat_1(X2)|~r2_hidden(X3,X1)|~r2_hidden(k4_tarski(X4,X3),X2)|~v2_wellord1(X2)|~r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_26, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_27, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_28, plain, (~v1_relat_1(X1)|~v2_wellord1(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_29, plain, (X1=k1_wellord1(k1_wellord2(X2),X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_30, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_21]), c_0_22])])).
% 0.19/0.38  cnf(c_0_31, plain, (v2_wellord1(k1_wellord2(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  fof(c_0_32, plain, ![X45, X46]:(~r1_tarski(X45,X46)|k2_wellord1(k1_wellord2(X46),X45)=k1_wellord2(X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).
% 0.19/0.38  fof(c_0_33, plain, ![X31, X32]:(~v1_relat_1(X31)|(~v1_relat_1(X32)|(~r4_wellord1(X31,X32)|r4_wellord1(X32,X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).
% 0.19/0.38  fof(c_0_34, negated_conjecture, (v3_ordinal1(esk8_0)&(v3_ordinal1(esk9_0)&(r4_wellord1(k1_wellord2(esk8_0),k1_wellord2(esk9_0))&esk8_0!=esk9_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.19/0.38  fof(c_0_35, plain, ![X13, X14]:(~v3_ordinal1(X13)|(~v3_ordinal1(X14)|(r2_hidden(X13,X14)|X13=X14|r2_hidden(X14,X13)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 0.19/0.38  cnf(c_0_36, plain, (r2_hidden(X1,k3_relat_1(X2))|~v2_wellord1(X2)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X3,k3_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_25]), c_0_26])])).
% 0.19/0.38  cnf(c_0_37, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)|~r2_hidden(X1,k1_wellord1(X3,X2))), inference(er,[status(thm)],[c_0_27])).
% 0.19/0.38  cnf(c_0_38, plain, (~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),X2))|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X2,X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_22])]), c_0_30])]), c_0_31])).
% 0.19/0.38  cnf(c_0_39, plain, (k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  cnf(c_0_40, plain, (r4_wellord1(X2,X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r4_wellord1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (r4_wellord1(k1_wellord2(esk8_0),k1_wellord2(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.38  cnf(c_0_42, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (v3_ordinal1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.38  cnf(c_0_44, plain, (r2_hidden(X1,k3_relat_1(X2))|~v2_wellord1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_wellord1(X2,X3))|~r2_hidden(X3,k3_relat_1(X2))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.38  fof(c_0_45, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.38  cnf(c_0_46, plain, (~r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X2,X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (r4_wellord1(k1_wellord2(esk9_0),k1_wellord2(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_22]), c_0_22])])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (v3_ordinal1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (X1=esk9_0|r2_hidden(esk9_0,X1)|r2_hidden(X1,esk9_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (esk8_0!=esk9_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.38  cnf(c_0_51, plain, (r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X3)|~r2_hidden(X1,X3)|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_29]), c_0_30]), c_0_22]), c_0_30])]), c_0_31])).
% 0.19/0.38  cnf(c_0_52, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (~r2_hidden(esk8_0,esk9_0)|~r1_tarski(esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_43]), c_0_48])])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (r2_hidden(esk8_0,esk9_0)|r2_hidden(esk9_0,esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_48]), c_0_50])).
% 0.19/0.38  cnf(c_0_55, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.38  cnf(c_0_56, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~v3_ordinal1(X3)|~v3_ordinal1(X1)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (~r2_hidden(esk9_0,esk8_0)|~r1_tarski(esk9_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_41]), c_0_48]), c_0_43])])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (r2_hidden(esk9_0,esk8_0)|~r1_tarski(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.38  cnf(c_0_59, plain, (r1_tarski(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.38  cnf(c_0_60, negated_conjecture, (~r1_tarski(esk9_0,esk8_0)|~r1_tarski(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (~r1_tarski(esk8_0,esk9_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_58]), c_0_48]), c_0_43])]), c_0_60])).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (r2_hidden(esk9_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_54]), c_0_43]), c_0_48])]), c_0_61])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (~r1_tarski(esk9_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_62])])).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_62]), c_0_48]), c_0_43])]), c_0_63]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 65
% 0.19/0.38  # Proof object clause steps            : 38
% 0.19/0.38  # Proof object formula steps           : 27
% 0.19/0.38  # Proof object conjectures             : 18
% 0.19/0.38  # Proof object clause conjectures      : 15
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 17
% 0.19/0.38  # Proof object initial formulas used   : 13
% 0.19/0.38  # Proof object generating inferences   : 16
% 0.19/0.38  # Proof object simplifying inferences  : 42
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 13
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 38
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 38
% 0.19/0.38  # Processed clauses                    : 97
% 0.19/0.38  # ...of these trivial                  : 2
% 0.19/0.38  # ...subsumed                          : 9
% 0.19/0.38  # ...remaining for further processing  : 85
% 0.19/0.38  # Other redundant clauses eliminated   : 15
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 5
% 0.19/0.38  # Backward-rewritten                   : 3
% 0.19/0.38  # Generated clauses                    : 147
% 0.19/0.38  # ...of the previous two non-trivial   : 139
% 0.19/0.38  # Contextual simplify-reflections      : 10
% 0.19/0.38  # Paramodulations                      : 133
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 15
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 63
% 0.19/0.38  #    Positive orientable unit clauses  : 8
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 4
% 0.19/0.38  #    Non-unit-clauses                  : 51
% 0.19/0.38  # Current number of unprocessed clauses: 80
% 0.19/0.38  # ...number of literals in the above   : 511
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 8
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 564
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 147
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 22
% 0.19/0.38  # Unit Clause-clause subsumption calls : 37
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 6
% 0.19/0.38  # BW rewrite match successes           : 1
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 6249
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.037 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.041 s
% 0.19/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
