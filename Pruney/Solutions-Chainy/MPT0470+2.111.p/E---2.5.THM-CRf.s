%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:10 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 242 expanded)
%              Number of clauses        :   44 ( 115 expanded)
%              Number of leaves         :   11 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  291 (1171 expanded)
%              Number of equality atoms :   85 ( 271 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(t56_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),X1)
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t62_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(c_0_11,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_xboole_0(X7,X8) )
      & ( r2_hidden(esk1_2(X7,X8),X8)
        | r1_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_12,plain,(
    ! [X22,X23,X24,X25,X26,X28,X29,X30,X33] :
      ( ( r2_hidden(k4_tarski(X25,esk2_5(X22,X23,X24,X25,X26)),X22)
        | ~ r2_hidden(k4_tarski(X25,X26),X24)
        | X24 != k5_relat_1(X22,X23)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(k4_tarski(esk2_5(X22,X23,X24,X25,X26),X26),X23)
        | ~ r2_hidden(k4_tarski(X25,X26),X24)
        | X24 != k5_relat_1(X22,X23)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22) )
      & ( ~ r2_hidden(k4_tarski(X28,X30),X22)
        | ~ r2_hidden(k4_tarski(X30,X29),X23)
        | r2_hidden(k4_tarski(X28,X29),X24)
        | X24 != k5_relat_1(X22,X23)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22) )
      & ( ~ r2_hidden(k4_tarski(esk3_3(X22,X23,X24),esk4_3(X22,X23,X24)),X24)
        | ~ r2_hidden(k4_tarski(esk3_3(X22,X23,X24),X33),X22)
        | ~ r2_hidden(k4_tarski(X33,esk4_3(X22,X23,X24)),X23)
        | X24 = k5_relat_1(X22,X23)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(k4_tarski(esk3_3(X22,X23,X24),esk5_3(X22,X23,X24)),X22)
        | r2_hidden(k4_tarski(esk3_3(X22,X23,X24),esk4_3(X22,X23,X24)),X24)
        | X24 = k5_relat_1(X22,X23)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(k4_tarski(esk5_3(X22,X23,X24),esk4_3(X22,X23,X24)),X23)
        | r2_hidden(k4_tarski(esk3_3(X22,X23,X24),esk4_3(X22,X23,X24)),X24)
        | X24 = k5_relat_1(X22,X23)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,esk2_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( X1 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,esk2_5(X2,X3,X1,X4,X5)),X6)
    | ~ r2_hidden(k4_tarski(X4,X5),X1)
    | ~ r1_xboole_0(X6,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_16,plain,(
    ! [X39] :
      ( ~ v1_relat_1(X39)
      | r2_hidden(k4_tarski(esk6_1(X39),esk7_1(X39)),X39)
      | X39 = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).

cnf(c_0_17,plain,
    ( X1 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X1)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(esk2_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(esk6_1(X1),esk7_1(X1)),X1)
    | X1 = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X35)
      | ~ v1_relat_1(X36)
      | v1_relat_1(k5_relat_1(X35,X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_21,plain,(
    ! [X18,X19] :
      ( ( ~ r1_xboole_0(X18,X19)
        | k4_xboole_0(X18,X19) = X18 )
      & ( k4_xboole_0(X18,X19) != X18
        | r1_xboole_0(X18,X19) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_22,plain,(
    ! [X15,X16] :
      ( ( k4_xboole_0(X15,X16) != k1_xboole_0
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | k4_xboole_0(X15,X16) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_23,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | X13 != X14 )
      & ( r1_tarski(X14,X13)
        | X13 != X14 )
      & ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,X13)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_24,plain,
    ( X1 != k5_relat_1(X2,X3)
    | X4 != k5_relat_1(X5,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5)
    | ~ r2_hidden(k4_tarski(X6,X7),X4)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | X1 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_19])).

cnf(c_0_26,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | X2 != k5_relat_1(X3,X4)
    | X1 != k5_relat_1(X5,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X5)
    | ~ r1_xboole_0(X3,X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_19])).

cnf(c_0_32,plain,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X1,X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_26])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_27])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,X2)
    | k1_xboole_0 != X1
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X37)
      | v1_relat_1(k3_xboole_0(X37,X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

fof(c_0_37,plain,(
    ! [X20,X21] : k1_setfam_1(k2_tarski(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_38,plain,(
    ! [X17] : k3_xboole_0(X17,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_39,plain,
    ( X1 != k5_relat_1(X2,X3)
    | X4 != k5_relat_1(X1,X5)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5)
    | ~ r2_hidden(k4_tarski(X6,X7),X4)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_14])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | X1 != k5_relat_1(X2,X3)
    | X3 != k1_xboole_0
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_xboole_0(X5,X5) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_27])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,X1)
    | k1_xboole_0 != X1 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_43,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
          & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t62_relat_1])).

cnf(c_0_44,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | X2 != k5_relat_1(X3,X4)
    | X1 != k5_relat_1(X2,X5)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X5)
    | ~ r1_xboole_0(X3,X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_19])).

cnf(c_0_48,plain,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | X2 != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X4,X4) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_40]),c_0_26])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,X2)
    | k1_xboole_0 != X2 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_50,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & ( k5_relat_1(k1_xboole_0,esk8_0) != k1_xboole_0
      | k5_relat_1(esk8_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).

cnf(c_0_51,plain,
    ( v1_relat_1(k1_setfam_1(k2_tarski(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_46,c_0_45])).

cnf(c_0_53,plain,
    ( X1 = k1_xboole_0
    | X1 != k5_relat_1(X2,X3)
    | X2 != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ r1_xboole_0(X5,X5) ),
    inference(spm,[status(thm)],[c_0_47,c_0_32])).

cnf(c_0_54,plain,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | X2 != k1_xboole_0
    | k1_xboole_0 != X3
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,plain,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2)
    | ~ r1_xboole_0(X4,X4) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_53]),c_0_26])).

cnf(c_0_58,negated_conjecture,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | X2 != k1_xboole_0
    | k1_xboole_0 != X3
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_55])).

cnf(c_0_60,plain,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0
    | k1_xboole_0 != X3
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_49])).

cnf(c_0_61,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk8_0) != k1_xboole_0
    | k5_relat_1(esk8_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,negated_conjecture,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | X2 != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0
    | k1_xboole_0 != X3
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk8_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_59]),c_0_55])])).

cnf(c_0_65,negated_conjecture,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_59]),c_0_55])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:54:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.14/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.14/0.38  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 0.14/0.38  fof(t56_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(![X2, X3]:~(r2_hidden(k4_tarski(X2,X3),X1))=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 0.14/0.38  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.14/0.38  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.14/0.38  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.14/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.14/0.38  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.14/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.14/0.38  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.14/0.38  fof(t62_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 0.14/0.38  fof(c_0_11, plain, ![X7, X8, X10, X11, X12]:(((r2_hidden(esk1_2(X7,X8),X7)|r1_xboole_0(X7,X8))&(r2_hidden(esk1_2(X7,X8),X8)|r1_xboole_0(X7,X8)))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|~r1_xboole_0(X10,X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.14/0.38  fof(c_0_12, plain, ![X22, X23, X24, X25, X26, X28, X29, X30, X33]:((((r2_hidden(k4_tarski(X25,esk2_5(X22,X23,X24,X25,X26)),X22)|~r2_hidden(k4_tarski(X25,X26),X24)|X24!=k5_relat_1(X22,X23)|~v1_relat_1(X24)|~v1_relat_1(X23)|~v1_relat_1(X22))&(r2_hidden(k4_tarski(esk2_5(X22,X23,X24,X25,X26),X26),X23)|~r2_hidden(k4_tarski(X25,X26),X24)|X24!=k5_relat_1(X22,X23)|~v1_relat_1(X24)|~v1_relat_1(X23)|~v1_relat_1(X22)))&(~r2_hidden(k4_tarski(X28,X30),X22)|~r2_hidden(k4_tarski(X30,X29),X23)|r2_hidden(k4_tarski(X28,X29),X24)|X24!=k5_relat_1(X22,X23)|~v1_relat_1(X24)|~v1_relat_1(X23)|~v1_relat_1(X22)))&((~r2_hidden(k4_tarski(esk3_3(X22,X23,X24),esk4_3(X22,X23,X24)),X24)|(~r2_hidden(k4_tarski(esk3_3(X22,X23,X24),X33),X22)|~r2_hidden(k4_tarski(X33,esk4_3(X22,X23,X24)),X23))|X24=k5_relat_1(X22,X23)|~v1_relat_1(X24)|~v1_relat_1(X23)|~v1_relat_1(X22))&((r2_hidden(k4_tarski(esk3_3(X22,X23,X24),esk5_3(X22,X23,X24)),X22)|r2_hidden(k4_tarski(esk3_3(X22,X23,X24),esk4_3(X22,X23,X24)),X24)|X24=k5_relat_1(X22,X23)|~v1_relat_1(X24)|~v1_relat_1(X23)|~v1_relat_1(X22))&(r2_hidden(k4_tarski(esk5_3(X22,X23,X24),esk4_3(X22,X23,X24)),X23)|r2_hidden(k4_tarski(esk3_3(X22,X23,X24),esk4_3(X22,X23,X24)),X24)|X24=k5_relat_1(X22,X23)|~v1_relat_1(X24)|~v1_relat_1(X23)|~v1_relat_1(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.14/0.38  cnf(c_0_13, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,esk2_5(X2,X3,X4,X1,X5)),X2)|~r2_hidden(k4_tarski(X1,X5),X4)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_15, plain, (X1!=k5_relat_1(X2,X3)|~v1_relat_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X4,esk2_5(X2,X3,X1,X4,X5)),X6)|~r2_hidden(k4_tarski(X4,X5),X1)|~r1_xboole_0(X6,X2)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.38  fof(c_0_16, plain, ![X39]:(~v1_relat_1(X39)|(r2_hidden(k4_tarski(esk6_1(X39),esk7_1(X39)),X39)|X39=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).
% 0.14/0.38  cnf(c_0_17, plain, (X1!=k5_relat_1(X2,X3)|~v1_relat_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X4,X5),X1)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_15, c_0_14])).
% 0.14/0.38  cnf(c_0_18, plain, (r2_hidden(k4_tarski(esk2_5(X1,X2,X3,X4,X5),X5),X2)|~r2_hidden(k4_tarski(X4,X5),X3)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_19, plain, (r2_hidden(k4_tarski(esk6_1(X1),esk7_1(X1)),X1)|X1=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  fof(c_0_20, plain, ![X35, X36]:(~v1_relat_1(X35)|~v1_relat_1(X36)|v1_relat_1(k5_relat_1(X35,X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.14/0.38  fof(c_0_21, plain, ![X18, X19]:((~r1_xboole_0(X18,X19)|k4_xboole_0(X18,X19)=X18)&(k4_xboole_0(X18,X19)!=X18|r1_xboole_0(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.14/0.38  fof(c_0_22, plain, ![X15, X16]:((k4_xboole_0(X15,X16)!=k1_xboole_0|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|k4_xboole_0(X15,X16)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.14/0.38  fof(c_0_23, plain, ![X13, X14]:(((r1_tarski(X13,X14)|X13!=X14)&(r1_tarski(X14,X13)|X13!=X14))&(~r1_tarski(X13,X14)|~r1_tarski(X14,X13)|X13=X14)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.14/0.38  cnf(c_0_24, plain, (X1!=k5_relat_1(X2,X3)|X4!=k5_relat_1(X5,X1)|~v1_relat_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X4)|~v1_relat_1(X5)|~r2_hidden(k4_tarski(X6,X7),X4)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.14/0.38  cnf(c_0_25, plain, (X1=k1_xboole_0|X1!=k5_relat_1(X2,X3)|~v1_relat_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_17, c_0_19])).
% 0.14/0.38  cnf(c_0_26, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  cnf(c_0_27, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_28, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_30, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.38  cnf(c_0_31, plain, (X1=k1_xboole_0|X2!=k5_relat_1(X3,X4)|X1!=k5_relat_1(X5,X2)|~v1_relat_1(X2)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X1)|~v1_relat_1(X5)|~r1_xboole_0(X3,X3)), inference(spm,[status(thm)],[c_0_24, c_0_19])).
% 0.14/0.38  cnf(c_0_32, plain, (k5_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_xboole_0(X1,X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]), c_0_26])).
% 0.14/0.38  cnf(c_0_33, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_13, c_0_27])).
% 0.14/0.38  cnf(c_0_34, plain, (r1_xboole_0(X1,X2)|k1_xboole_0!=X1|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.14/0.38  cnf(c_0_35, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_30])).
% 0.14/0.38  fof(c_0_36, plain, ![X37, X38]:(~v1_relat_1(X37)|v1_relat_1(k3_xboole_0(X37,X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.14/0.38  fof(c_0_37, plain, ![X20, X21]:k1_setfam_1(k2_tarski(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.14/0.38  fof(c_0_38, plain, ![X17]:k3_xboole_0(X17,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.14/0.38  cnf(c_0_39, plain, (X1!=k5_relat_1(X2,X3)|X4!=k5_relat_1(X1,X5)|~v1_relat_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X4)|~v1_relat_1(X5)|~r2_hidden(k4_tarski(X6,X7),X4)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_17, c_0_14])).
% 0.14/0.38  cnf(c_0_40, plain, (X1=k1_xboole_0|X1!=k5_relat_1(X2,X3)|X3!=k1_xboole_0|~v1_relat_1(X3)|~v1_relat_1(X4)|~v1_relat_1(X5)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_xboole_0(X5,X5)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.14/0.38  cnf(c_0_41, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_33, c_0_27])).
% 0.14/0.38  cnf(c_0_42, plain, (r1_xboole_0(X1,X1)|k1_xboole_0!=X1), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.14/0.38  fof(c_0_43, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t62_relat_1])).
% 0.14/0.38  cnf(c_0_44, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.38  cnf(c_0_45, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.14/0.38  cnf(c_0_46, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.38  cnf(c_0_47, plain, (X1=k1_xboole_0|X2!=k5_relat_1(X3,X4)|X1!=k5_relat_1(X2,X5)|~v1_relat_1(X2)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X1)|~v1_relat_1(X5)|~r1_xboole_0(X3,X3)), inference(spm,[status(thm)],[c_0_39, c_0_19])).
% 0.14/0.38  cnf(c_0_48, plain, (k5_relat_1(X1,X2)=k1_xboole_0|X2!=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X3)|~v1_relat_1(X4)|~v1_relat_1(X1)|~r1_xboole_0(X4,X4)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_40]), c_0_26])).
% 0.14/0.38  cnf(c_0_49, plain, (r1_xboole_0(X1,X2)|k1_xboole_0!=X2), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.14/0.38  fof(c_0_50, negated_conjecture, (v1_relat_1(esk8_0)&(k5_relat_1(k1_xboole_0,esk8_0)!=k1_xboole_0|k5_relat_1(esk8_0,k1_xboole_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).
% 0.14/0.38  cnf(c_0_51, plain, (v1_relat_1(k1_setfam_1(k2_tarski(X1,X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.14/0.38  cnf(c_0_52, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_46, c_0_45])).
% 0.14/0.38  cnf(c_0_53, plain, (X1=k1_xboole_0|X1!=k5_relat_1(X2,X3)|X2!=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X4)|~v1_relat_1(X5)|~v1_relat_1(X1)|~v1_relat_1(X3)|~r1_xboole_0(X5,X5)), inference(spm,[status(thm)],[c_0_47, c_0_32])).
% 0.14/0.38  cnf(c_0_54, plain, (k5_relat_1(X1,X2)=k1_xboole_0|X2!=k1_xboole_0|k1_xboole_0!=X3|~v1_relat_1(X2)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.14/0.38  cnf(c_0_55, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.14/0.38  cnf(c_0_56, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.14/0.38  cnf(c_0_57, plain, (k5_relat_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0|~v1_relat_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X4)|~v1_relat_1(X2)|~r1_xboole_0(X4,X4)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_53]), c_0_26])).
% 0.14/0.38  cnf(c_0_58, negated_conjecture, (k5_relat_1(X1,X2)=k1_xboole_0|X2!=k1_xboole_0|k1_xboole_0!=X3|~v1_relat_1(X2)|~v1_relat_1(X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.14/0.38  cnf(c_0_59, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_55])).
% 0.14/0.38  cnf(c_0_60, plain, (k5_relat_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0|k1_xboole_0!=X3|~v1_relat_1(X1)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_57, c_0_49])).
% 0.14/0.38  cnf(c_0_61, negated_conjecture, (k5_relat_1(k1_xboole_0,esk8_0)!=k1_xboole_0|k5_relat_1(esk8_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.14/0.38  cnf(c_0_62, negated_conjecture, (k5_relat_1(X1,X2)=k1_xboole_0|X2!=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.14/0.38  cnf(c_0_63, negated_conjecture, (k5_relat_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0|k1_xboole_0!=X3|~v1_relat_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_60, c_0_55])).
% 0.14/0.38  cnf(c_0_64, negated_conjecture, (k5_relat_1(k1_xboole_0,esk8_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_59]), c_0_55])])).
% 0.14/0.38  cnf(c_0_65, negated_conjecture, (k5_relat_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_63, c_0_59])).
% 0.14/0.38  cnf(c_0_66, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_59]), c_0_55])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 67
% 0.14/0.38  # Proof object clause steps            : 44
% 0.14/0.38  # Proof object formula steps           : 23
% 0.14/0.38  # Proof object conjectures             : 12
% 0.14/0.38  # Proof object clause conjectures      : 9
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 14
% 0.14/0.38  # Proof object initial formulas used   : 11
% 0.14/0.38  # Proof object generating inferences   : 27
% 0.14/0.38  # Proof object simplifying inferences  : 12
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 11
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 23
% 0.14/0.38  # Removed in clause preprocessing      : 1
% 0.14/0.38  # Initial clauses in saturation        : 22
% 0.14/0.38  # Processed clauses                    : 98
% 0.14/0.38  # ...of these trivial                  : 1
% 0.14/0.38  # ...subsumed                          : 13
% 0.14/0.38  # ...remaining for further processing  : 84
% 0.14/0.38  # Other redundant clauses eliminated   : 2
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 9
% 0.14/0.38  # Backward-rewritten                   : 1
% 0.14/0.38  # Generated clauses                    : 109
% 0.14/0.38  # ...of the previous two non-trivial   : 86
% 0.14/0.38  # Contextual simplify-reflections      : 3
% 0.14/0.38  # Paramodulations                      : 102
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 7
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 51
% 0.14/0.38  #    Positive orientable unit clauses  : 4
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 3
% 0.14/0.38  #    Non-unit-clauses                  : 44
% 0.14/0.38  # Current number of unprocessed clauses: 22
% 0.14/0.38  # ...number of literals in the above   : 183
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 32
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 1258
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 429
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 20
% 0.14/0.38  # Unit Clause-clause subsumption calls : 29
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 1
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 3673
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.033 s
% 0.14/0.38  # System time              : 0.004 s
% 0.14/0.38  # Total time               : 0.038 s
% 0.14/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
