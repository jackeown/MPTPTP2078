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
% DateTime   : Thu Dec  3 11:00:43 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 813 expanded)
%              Number of clauses        :   39 ( 332 expanded)
%              Number of leaves         :   13 ( 216 expanded)
%              Depth                    :   12
%              Number of atoms          :  325 (3616 expanded)
%              Number of equality atoms :   63 ( 853 expanded)
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

fof(t41_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ( ! [X3] :
                ( ( r2_hidden(X3,k3_relat_1(X1))
                  & r1_tarski(k1_wellord1(X1,X3),X2) )
               => r2_hidden(X3,X2) )
           => r1_tarski(k3_relat_1(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_wellord1)).

fof(c_0_13,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_14,plain,(
    ! [X32,X33,X34,X35] :
      ( ( k3_relat_1(X33) = X32
        | X33 != k1_wellord2(X32)
        | ~ v1_relat_1(X33) )
      & ( ~ r2_hidden(k4_tarski(X34,X35),X33)
        | r1_tarski(X34,X35)
        | ~ r2_hidden(X34,X32)
        | ~ r2_hidden(X35,X32)
        | X33 != k1_wellord2(X32)
        | ~ v1_relat_1(X33) )
      & ( ~ r1_tarski(X34,X35)
        | r2_hidden(k4_tarski(X34,X35),X33)
        | ~ r2_hidden(X34,X32)
        | ~ r2_hidden(X35,X32)
        | X33 != k1_wellord2(X32)
        | ~ v1_relat_1(X33) )
      & ( r2_hidden(esk6_2(X32,X33),X32)
        | k3_relat_1(X33) != X32
        | X33 = k1_wellord2(X32)
        | ~ v1_relat_1(X33) )
      & ( r2_hidden(esk7_2(X32,X33),X32)
        | k3_relat_1(X33) != X32
        | X33 = k1_wellord2(X32)
        | ~ v1_relat_1(X33) )
      & ( ~ r2_hidden(k4_tarski(esk6_2(X32,X33),esk7_2(X32,X33)),X33)
        | ~ r1_tarski(esk6_2(X32,X33),esk7_2(X32,X33))
        | k3_relat_1(X33) != X32
        | X33 = k1_wellord2(X32)
        | ~ v1_relat_1(X33) )
      & ( r2_hidden(k4_tarski(esk6_2(X32,X33),esk7_2(X32,X33)),X33)
        | r1_tarski(esk6_2(X32,X33),esk7_2(X32,X33))
        | k3_relat_1(X33) != X32
        | X33 = k1_wellord2(X32)
        | ~ v1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_15,plain,(
    ! [X38] : v1_relat_1(k1_wellord2(X38)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_16,plain,(
    ! [X17,X18,X19,X20,X21] :
      ( ( X17 != k3_relat_1(X18)
        | ~ r2_hidden(X20,X17)
        | ~ r2_hidden(k4_tarski(X21,X20),X18)
        | r2_hidden(X21,X17)
        | ~ v2_wellord1(X18)
        | ~ r1_tarski(X17,k3_relat_1(X18))
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(X19,k3_relat_1(X18))
        | X17 != k1_wellord1(X18,X19)
        | ~ r2_hidden(X20,X17)
        | ~ r2_hidden(k4_tarski(X21,X20),X18)
        | r2_hidden(X21,X17)
        | ~ v2_wellord1(X18)
        | ~ r1_tarski(X17,k3_relat_1(X18))
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(esk4_2(X17,X18),k3_relat_1(X18))
        | X17 = k3_relat_1(X18)
        | r2_hidden(esk2_2(X17,X18),X17)
        | ~ v2_wellord1(X18)
        | ~ r1_tarski(X17,k3_relat_1(X18))
        | ~ v1_relat_1(X18) )
      & ( X17 = k1_wellord1(X18,esk4_2(X17,X18))
        | X17 = k3_relat_1(X18)
        | r2_hidden(esk2_2(X17,X18),X17)
        | ~ v2_wellord1(X18)
        | ~ r1_tarski(X17,k3_relat_1(X18))
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(esk4_2(X17,X18),k3_relat_1(X18))
        | X17 = k3_relat_1(X18)
        | r2_hidden(k4_tarski(esk3_2(X17,X18),esk2_2(X17,X18)),X18)
        | ~ v2_wellord1(X18)
        | ~ r1_tarski(X17,k3_relat_1(X18))
        | ~ v1_relat_1(X18) )
      & ( X17 = k1_wellord1(X18,esk4_2(X17,X18))
        | X17 = k3_relat_1(X18)
        | r2_hidden(k4_tarski(esk3_2(X17,X18),esk2_2(X17,X18)),X18)
        | ~ v2_wellord1(X18)
        | ~ r1_tarski(X17,k3_relat_1(X18))
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(esk4_2(X17,X18),k3_relat_1(X18))
        | X17 = k3_relat_1(X18)
        | ~ r2_hidden(esk3_2(X17,X18),X17)
        | ~ v2_wellord1(X18)
        | ~ r1_tarski(X17,k3_relat_1(X18))
        | ~ v1_relat_1(X18) )
      & ( X17 = k1_wellord1(X18,esk4_2(X17,X18))
        | X17 = k3_relat_1(X18)
        | ~ r2_hidden(esk3_2(X17,X18),X17)
        | ~ v2_wellord1(X18)
        | ~ r1_tarski(X17,k3_relat_1(X18))
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_wellord1])])])])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15] :
      ( ( X12 != X10
        | ~ r2_hidden(X12,X11)
        | X11 != k1_wellord1(X9,X10)
        | ~ v1_relat_1(X9) )
      & ( r2_hidden(k4_tarski(X12,X10),X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k1_wellord1(X9,X10)
        | ~ v1_relat_1(X9) )
      & ( X13 = X10
        | ~ r2_hidden(k4_tarski(X13,X10),X9)
        | r2_hidden(X13,X11)
        | X11 != k1_wellord1(X9,X10)
        | ~ v1_relat_1(X9) )
      & ( ~ r2_hidden(esk1_3(X9,X14,X15),X15)
        | esk1_3(X9,X14,X15) = X14
        | ~ r2_hidden(k4_tarski(esk1_3(X9,X14,X15),X14),X9)
        | X15 = k1_wellord1(X9,X14)
        | ~ v1_relat_1(X9) )
      & ( esk1_3(X9,X14,X15) != X14
        | r2_hidden(esk1_3(X9,X14,X15),X15)
        | X15 = k1_wellord1(X9,X14)
        | ~ v1_relat_1(X9) )
      & ( r2_hidden(k4_tarski(esk1_3(X9,X14,X15),X14),X9)
        | r2_hidden(esk1_3(X9,X14,X15),X15)
        | X15 = k1_wellord1(X9,X14)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

fof(c_0_19,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X30)
      | ~ v2_wellord1(X30)
      | ~ r2_hidden(X31,k3_relat_1(X30))
      | ~ r4_wellord1(X30,k2_wellord1(X30,k1_wellord1(X30,X31))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).

fof(c_0_20,plain,(
    ! [X39,X40] :
      ( ~ v3_ordinal1(X39)
      | ~ v3_ordinal1(X40)
      | ~ r2_hidden(X39,X40)
      | X39 = k1_wellord1(k1_wellord2(X40),X39) ) ),
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
    ! [X41] :
      ( ~ v3_ordinal1(X41)
      | v2_wellord1(k1_wellord2(X41)) ) ),
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
    ! [X42,X43] :
      ( ~ r1_tarski(X42,X43)
      | k2_wellord1(k1_wellord2(X43),X42) = k1_wellord2(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).

fof(c_0_33,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X28)
      | ~ v1_relat_1(X29)
      | ~ r4_wellord1(X28,X29)
      | r4_wellord1(X29,X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).

fof(c_0_34,negated_conjecture,
    ( v3_ordinal1(esk8_0)
    & v3_ordinal1(esk9_0)
    & r4_wellord1(k1_wellord2(esk8_0),k1_wellord2(esk9_0))
    & esk8_0 != esk9_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_35,plain,(
    ! [X7,X8] :
      ( ~ v3_ordinal1(X7)
      | ~ v3_ordinal1(X8)
      | r2_hidden(X7,X8)
      | X7 = X8
      | r2_hidden(X8,X7) ) ),
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

fof(c_0_38,plain,(
    ! [X25,X26] :
      ( ( r2_hidden(esk5_2(X25,X26),k3_relat_1(X25))
        | r1_tarski(k3_relat_1(X25),X26)
        | ~ v2_wellord1(X25)
        | ~ v1_relat_1(X25) )
      & ( r1_tarski(k1_wellord1(X25,esk5_2(X25,X26)),X26)
        | r1_tarski(k3_relat_1(X25),X26)
        | ~ v2_wellord1(X25)
        | ~ v1_relat_1(X25) )
      & ( ~ r2_hidden(esk5_2(X25,X26),X26)
        | r1_tarski(k3_relat_1(X25),X26)
        | ~ v2_wellord1(X25)
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_wellord1])])])])])).

cnf(c_0_39,plain,
    ( ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),X2))
    | ~ r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_22])]),c_0_30])]),c_0_31])).

cnf(c_0_40,plain,
    ( k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r4_wellord1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk8_0),k1_wellord2(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( v3_ordinal1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_wellord1(X2,X3))
    | ~ r2_hidden(X3,k3_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_46,plain,
    ( r2_hidden(esk5_2(X1,X2),k3_relat_1(X1))
    | r1_tarski(k3_relat_1(X1),X2)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( ~ r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
    | ~ r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk9_0),k1_wellord2(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_22]),c_0_22])])).

cnf(c_0_49,negated_conjecture,
    ( v3_ordinal1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( X1 = esk9_0
    | r2_hidden(esk9_0,X1)
    | r2_hidden(X1,esk9_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( esk8_0 != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X3) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_29]),c_0_30]),c_0_22]),c_0_30])]),c_0_31])).

cnf(c_0_53,plain,
    ( r2_hidden(esk5_2(k1_wellord2(X1),X2),X1)
    | r1_tarski(X1,X2)
    | ~ v2_wellord1(k1_wellord2(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_30]),c_0_22])])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(esk8_0,esk9_0)
    | ~ r1_tarski(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_44]),c_0_49])])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk8_0,esk9_0)
    | r2_hidden(esk9_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_49]),c_0_51])).

cnf(c_0_56,plain,
    ( r1_tarski(k3_relat_1(X1),X2)
    | ~ r2_hidden(esk5_2(X1,X2),X2)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_57,plain,
    ( r2_hidden(esk5_2(k1_wellord2(X1),X2),X3)
    | r1_tarski(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ v3_ordinal1(X3)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_31])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(esk9_0,esk8_0)
    | ~ r1_tarski(esk9_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_42]),c_0_49]),c_0_44])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0)
    | ~ r1_tarski(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_30]),c_0_22])]),c_0_31])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(esk9_0,esk8_0)
    | ~ r1_tarski(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tarski(esk8_0,esk9_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_59]),c_0_49]),c_0_44])]),c_0_61])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_55]),c_0_44]),c_0_49])]),c_0_62])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tarski(esk9_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_63])])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_63]),c_0_49]),c_0_44])]),c_0_64]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.029 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.13/0.38  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.13/0.38  fof(t36_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>((v2_wellord1(X2)&r1_tarski(X1,k3_relat_1(X2)))=>(~((X1!=k3_relat_1(X2)&![X3]:~((r2_hidden(X3,k3_relat_1(X2))&X1=k1_wellord1(X2,X3)))))<=>![X3]:(r2_hidden(X3,X1)=>![X4]:(r2_hidden(k4_tarski(X4,X3),X2)=>r2_hidden(X4,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_wellord1)).
% 0.13/0.38  fof(d1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k1_wellord1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4!=X2&r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 0.13/0.38  fof(t57_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)=>![X2]:~((r2_hidden(X2,k3_relat_1(X1))&r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_wellord1)).
% 0.13/0.38  fof(t10_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>X1=k1_wellord1(k1_wellord2(X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_wellord2)).
% 0.13/0.38  fof(t7_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>v2_wellord1(k1_wellord2(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_wellord2)).
% 0.13/0.38  fof(t11_wellord2, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_wellord2)).
% 0.13/0.38  fof(t8_wellord2, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 0.13/0.38  fof(t50_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r4_wellord1(X1,X2)=>r4_wellord1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_wellord1)).
% 0.13/0.38  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 0.13/0.38  fof(t41_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)=>![X2]:(![X3]:((r2_hidden(X3,k3_relat_1(X1))&r1_tarski(k1_wellord1(X1,X3),X2))=>r2_hidden(X3,X2))=>r1_tarski(k3_relat_1(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_wellord1)).
% 0.13/0.38  fof(c_0_13, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X32, X33, X34, X35]:(((k3_relat_1(X33)=X32|X33!=k1_wellord2(X32)|~v1_relat_1(X33))&((~r2_hidden(k4_tarski(X34,X35),X33)|r1_tarski(X34,X35)|(~r2_hidden(X34,X32)|~r2_hidden(X35,X32))|X33!=k1_wellord2(X32)|~v1_relat_1(X33))&(~r1_tarski(X34,X35)|r2_hidden(k4_tarski(X34,X35),X33)|(~r2_hidden(X34,X32)|~r2_hidden(X35,X32))|X33!=k1_wellord2(X32)|~v1_relat_1(X33))))&(((r2_hidden(esk6_2(X32,X33),X32)|k3_relat_1(X33)!=X32|X33=k1_wellord2(X32)|~v1_relat_1(X33))&(r2_hidden(esk7_2(X32,X33),X32)|k3_relat_1(X33)!=X32|X33=k1_wellord2(X32)|~v1_relat_1(X33)))&((~r2_hidden(k4_tarski(esk6_2(X32,X33),esk7_2(X32,X33)),X33)|~r1_tarski(esk6_2(X32,X33),esk7_2(X32,X33))|k3_relat_1(X33)!=X32|X33=k1_wellord2(X32)|~v1_relat_1(X33))&(r2_hidden(k4_tarski(esk6_2(X32,X33),esk7_2(X32,X33)),X33)|r1_tarski(esk6_2(X32,X33),esk7_2(X32,X33))|k3_relat_1(X33)!=X32|X33=k1_wellord2(X32)|~v1_relat_1(X33))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.13/0.38  fof(c_0_15, plain, ![X38]:v1_relat_1(k1_wellord2(X38)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.13/0.38  fof(c_0_16, plain, ![X17, X18, X19, X20, X21]:(((X17!=k3_relat_1(X18)|(~r2_hidden(X20,X17)|(~r2_hidden(k4_tarski(X21,X20),X18)|r2_hidden(X21,X17)))|(~v2_wellord1(X18)|~r1_tarski(X17,k3_relat_1(X18)))|~v1_relat_1(X18))&(~r2_hidden(X19,k3_relat_1(X18))|X17!=k1_wellord1(X18,X19)|(~r2_hidden(X20,X17)|(~r2_hidden(k4_tarski(X21,X20),X18)|r2_hidden(X21,X17)))|(~v2_wellord1(X18)|~r1_tarski(X17,k3_relat_1(X18)))|~v1_relat_1(X18)))&(((r2_hidden(esk4_2(X17,X18),k3_relat_1(X18))|X17=k3_relat_1(X18)|r2_hidden(esk2_2(X17,X18),X17)|(~v2_wellord1(X18)|~r1_tarski(X17,k3_relat_1(X18)))|~v1_relat_1(X18))&(X17=k1_wellord1(X18,esk4_2(X17,X18))|X17=k3_relat_1(X18)|r2_hidden(esk2_2(X17,X18),X17)|(~v2_wellord1(X18)|~r1_tarski(X17,k3_relat_1(X18)))|~v1_relat_1(X18)))&(((r2_hidden(esk4_2(X17,X18),k3_relat_1(X18))|X17=k3_relat_1(X18)|r2_hidden(k4_tarski(esk3_2(X17,X18),esk2_2(X17,X18)),X18)|(~v2_wellord1(X18)|~r1_tarski(X17,k3_relat_1(X18)))|~v1_relat_1(X18))&(X17=k1_wellord1(X18,esk4_2(X17,X18))|X17=k3_relat_1(X18)|r2_hidden(k4_tarski(esk3_2(X17,X18),esk2_2(X17,X18)),X18)|(~v2_wellord1(X18)|~r1_tarski(X17,k3_relat_1(X18)))|~v1_relat_1(X18)))&((r2_hidden(esk4_2(X17,X18),k3_relat_1(X18))|X17=k3_relat_1(X18)|~r2_hidden(esk3_2(X17,X18),X17)|(~v2_wellord1(X18)|~r1_tarski(X17,k3_relat_1(X18)))|~v1_relat_1(X18))&(X17=k1_wellord1(X18,esk4_2(X17,X18))|X17=k3_relat_1(X18)|~r2_hidden(esk3_2(X17,X18),X17)|(~v2_wellord1(X18)|~r1_tarski(X17,k3_relat_1(X18)))|~v1_relat_1(X18)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_wellord1])])])])])).
% 0.13/0.38  cnf(c_0_17, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_18, plain, ![X9, X10, X11, X12, X13, X14, X15]:((((X12!=X10|~r2_hidden(X12,X11)|X11!=k1_wellord1(X9,X10)|~v1_relat_1(X9))&(r2_hidden(k4_tarski(X12,X10),X9)|~r2_hidden(X12,X11)|X11!=k1_wellord1(X9,X10)|~v1_relat_1(X9)))&(X13=X10|~r2_hidden(k4_tarski(X13,X10),X9)|r2_hidden(X13,X11)|X11!=k1_wellord1(X9,X10)|~v1_relat_1(X9)))&((~r2_hidden(esk1_3(X9,X14,X15),X15)|(esk1_3(X9,X14,X15)=X14|~r2_hidden(k4_tarski(esk1_3(X9,X14,X15),X14),X9))|X15=k1_wellord1(X9,X14)|~v1_relat_1(X9))&((esk1_3(X9,X14,X15)!=X14|r2_hidden(esk1_3(X9,X14,X15),X15)|X15=k1_wellord1(X9,X14)|~v1_relat_1(X9))&(r2_hidden(k4_tarski(esk1_3(X9,X14,X15),X14),X9)|r2_hidden(esk1_3(X9,X14,X15),X15)|X15=k1_wellord1(X9,X14)|~v1_relat_1(X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).
% 0.13/0.38  fof(c_0_19, plain, ![X30, X31]:(~v1_relat_1(X30)|(~v2_wellord1(X30)|(~r2_hidden(X31,k3_relat_1(X30))|~r4_wellord1(X30,k2_wellord1(X30,k1_wellord1(X30,X31)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).
% 0.13/0.38  fof(c_0_20, plain, ![X39, X40]:(~v3_ordinal1(X39)|(~v3_ordinal1(X40)|(~r2_hidden(X39,X40)|X39=k1_wellord1(k1_wellord2(X40),X39)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).
% 0.13/0.38  cnf(c_0_21, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_22, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  fof(c_0_23, plain, ![X41]:(~v3_ordinal1(X41)|v2_wellord1(k1_wellord2(X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).
% 0.13/0.38  fof(c_0_24, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2)))), inference(assume_negation,[status(cth)],[t11_wellord2])).
% 0.13/0.38  cnf(c_0_25, plain, (r2_hidden(X4,X1)|X1!=k3_relat_1(X2)|~r2_hidden(X3,X1)|~r2_hidden(k4_tarski(X4,X3),X2)|~v2_wellord1(X2)|~r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_26, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_27, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_28, plain, (~v1_relat_1(X1)|~v2_wellord1(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_29, plain, (X1=k1_wellord1(k1_wellord2(X2),X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_30, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_21]), c_0_22])])).
% 0.13/0.38  cnf(c_0_31, plain, (v2_wellord1(k1_wellord2(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  fof(c_0_32, plain, ![X42, X43]:(~r1_tarski(X42,X43)|k2_wellord1(k1_wellord2(X43),X42)=k1_wellord2(X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).
% 0.13/0.38  fof(c_0_33, plain, ![X28, X29]:(~v1_relat_1(X28)|(~v1_relat_1(X29)|(~r4_wellord1(X28,X29)|r4_wellord1(X29,X28)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).
% 0.13/0.38  fof(c_0_34, negated_conjecture, (v3_ordinal1(esk8_0)&(v3_ordinal1(esk9_0)&(r4_wellord1(k1_wellord2(esk8_0),k1_wellord2(esk9_0))&esk8_0!=esk9_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.13/0.38  fof(c_0_35, plain, ![X7, X8]:(~v3_ordinal1(X7)|(~v3_ordinal1(X8)|(r2_hidden(X7,X8)|X7=X8|r2_hidden(X8,X7)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 0.13/0.38  cnf(c_0_36, plain, (r2_hidden(X1,k3_relat_1(X2))|~v2_wellord1(X2)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X3,k3_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_25]), c_0_26])])).
% 0.13/0.38  cnf(c_0_37, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)|~r2_hidden(X1,k1_wellord1(X3,X2))), inference(er,[status(thm)],[c_0_27])).
% 0.13/0.38  fof(c_0_38, plain, ![X25, X26]:(((r2_hidden(esk5_2(X25,X26),k3_relat_1(X25))|r1_tarski(k3_relat_1(X25),X26)|~v2_wellord1(X25)|~v1_relat_1(X25))&(r1_tarski(k1_wellord1(X25,esk5_2(X25,X26)),X26)|r1_tarski(k3_relat_1(X25),X26)|~v2_wellord1(X25)|~v1_relat_1(X25)))&(~r2_hidden(esk5_2(X25,X26),X26)|r1_tarski(k3_relat_1(X25),X26)|~v2_wellord1(X25)|~v1_relat_1(X25))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_wellord1])])])])])).
% 0.13/0.38  cnf(c_0_39, plain, (~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),X2))|~r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_22])]), c_0_30])]), c_0_31])).
% 0.13/0.38  cnf(c_0_40, plain, (k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_41, plain, (r4_wellord1(X2,X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r4_wellord1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (r4_wellord1(k1_wellord2(esk8_0),k1_wellord2(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_43, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (v3_ordinal1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_45, plain, (r2_hidden(X1,k3_relat_1(X2))|~v2_wellord1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_wellord1(X2,X3))|~r2_hidden(X3,k3_relat_1(X2))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.38  cnf(c_0_46, plain, (r2_hidden(esk5_2(X1,X2),k3_relat_1(X1))|r1_tarski(k3_relat_1(X1),X2)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.38  cnf(c_0_47, plain, (~r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))|~r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (r4_wellord1(k1_wellord2(esk9_0),k1_wellord2(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_22]), c_0_22])])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (v3_ordinal1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (X1=esk9_0|r2_hidden(esk9_0,X1)|r2_hidden(X1,esk9_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (esk8_0!=esk9_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_52, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X3,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X3)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_29]), c_0_30]), c_0_22]), c_0_30])]), c_0_31])).
% 0.13/0.38  cnf(c_0_53, plain, (r2_hidden(esk5_2(k1_wellord2(X1),X2),X1)|r1_tarski(X1,X2)|~v2_wellord1(k1_wellord2(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_30]), c_0_22])])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (~r2_hidden(esk8_0,esk9_0)|~r1_tarski(esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_44]), c_0_49])])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (r2_hidden(esk8_0,esk9_0)|r2_hidden(esk9_0,esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_49]), c_0_51])).
% 0.13/0.38  cnf(c_0_56, plain, (r1_tarski(k3_relat_1(X1),X2)|~r2_hidden(esk5_2(X1,X2),X2)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.38  cnf(c_0_57, plain, (r2_hidden(esk5_2(k1_wellord2(X1),X2),X3)|r1_tarski(X1,X2)|~r2_hidden(X1,X3)|~v3_ordinal1(X3)|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_31])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (~r2_hidden(esk9_0,esk8_0)|~r1_tarski(esk9_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_42]), c_0_49]), c_0_44])])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (r2_hidden(esk9_0,esk8_0)|~r1_tarski(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.13/0.38  cnf(c_0_60, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_30]), c_0_22])]), c_0_31])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (~r1_tarski(esk9_0,esk8_0)|~r1_tarski(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (~r1_tarski(esk8_0,esk9_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_59]), c_0_49]), c_0_44])]), c_0_61])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (r2_hidden(esk9_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_55]), c_0_44]), c_0_49])]), c_0_62])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (~r1_tarski(esk9_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_63])])).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_63]), c_0_49]), c_0_44])]), c_0_64]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 66
% 0.13/0.38  # Proof object clause steps            : 39
% 0.13/0.38  # Proof object formula steps           : 27
% 0.13/0.38  # Proof object conjectures             : 18
% 0.13/0.38  # Proof object clause conjectures      : 15
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 17
% 0.13/0.38  # Proof object initial formulas used   : 13
% 0.13/0.38  # Proof object generating inferences   : 17
% 0.13/0.38  # Proof object simplifying inferences  : 49
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 13
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 38
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 38
% 0.13/0.38  # Processed clauses                    : 99
% 0.13/0.38  # ...of these trivial                  : 2
% 0.13/0.38  # ...subsumed                          : 9
% 0.13/0.38  # ...remaining for further processing  : 87
% 0.13/0.38  # Other redundant clauses eliminated   : 15
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 5
% 0.13/0.38  # Backward-rewritten                   : 3
% 0.13/0.38  # Generated clauses                    : 150
% 0.13/0.38  # ...of the previous two non-trivial   : 142
% 0.13/0.38  # Contextual simplify-reflections      : 12
% 0.13/0.38  # Paramodulations                      : 136
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 15
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 65
% 0.13/0.38  #    Positive orientable unit clauses  : 8
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 4
% 0.13/0.38  #    Non-unit-clauses                  : 53
% 0.13/0.38  # Current number of unprocessed clauses: 81
% 0.13/0.38  # ...number of literals in the above   : 546
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 8
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 470
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 94
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 24
% 0.13/0.38  # Unit Clause-clause subsumption calls : 47
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 7
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 6527
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.035 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.040 s
% 0.13/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
