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
% DateTime   : Thu Dec  3 10:53:45 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  121 (2840 expanded)
%              Number of clauses        :   84 (1110 expanded)
%              Number of leaves         :   18 ( 762 expanded)
%              Depth                    :   28
%              Number of atoms          :  378 (9622 expanded)
%              Number of equality atoms :  105 (2872 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t57_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k2_relat_1(X2)) )
       => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
          & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(t56_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k1_relat_1(X2)) )
       => ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
          & X1 = k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t12_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(t34_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( X2 = k6_relat_1(X1)
      <=> ( k1_relat_1(X2) = X1
          & ! [X3] :
              ( r2_hidden(X3,X1)
             => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t54_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(involutiveness_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k4_relat_1(k4_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(t45_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(t46_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(t22_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
           => k1_funct_1(k5_relat_1(X3,X2),X1) = k1_funct_1(X2,k1_funct_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ( v2_funct_1(X2)
            & r2_hidden(X1,k2_relat_1(X2)) )
         => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
            & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_funct_1])).

fof(c_0_19,plain,(
    ! [X33] :
      ( ~ v1_relat_1(X33)
      | ~ v1_funct_1(X33)
      | ~ v2_funct_1(X33)
      | k2_funct_1(X33) = k4_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & v2_funct_1(esk7_0)
    & r2_hidden(esk6_0,k2_relat_1(esk7_0))
    & ( esk6_0 != k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),esk6_0))
      | esk6_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk7_0),esk7_0),esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_21,plain,(
    ! [X45,X46] :
      ( ( X45 = k1_funct_1(k2_funct_1(X46),k1_funct_1(X46,X45))
        | ~ v2_funct_1(X46)
        | ~ r2_hidden(X45,k1_relat_1(X46))
        | ~ v1_relat_1(X46)
        | ~ v1_funct_1(X46) )
      & ( X45 = k1_funct_1(k5_relat_1(X46,k2_funct_1(X46)),X45)
        | ~ v2_funct_1(X46)
        | ~ r2_hidden(X45,k1_relat_1(X46))
        | ~ v1_relat_1(X46)
        | ~ v1_funct_1(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).

cnf(c_0_22,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( v2_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X34] :
      ( ( v1_relat_1(k2_funct_1(X34))
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( v1_funct_1(k2_funct_1(X34))
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_27,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | ~ v1_funct_1(X37)
      | ~ r2_hidden(X36,k1_relat_1(X37))
      | r2_hidden(k1_funct_1(X37,X36),k2_relat_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

cnf(c_0_28,plain,
    ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
    | ~ v2_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( k2_funct_1(esk7_0) = k4_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_30,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( k1_funct_1(k4_relat_1(esk7_0),k1_funct_1(esk7_0,X1)) = X1
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(k4_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_29]),c_0_24]),c_0_25])])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(k4_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_29]),c_0_24]),c_0_25])])).

fof(c_0_36,plain,(
    ! [X15] :
      ( ( k2_relat_1(X15) = k1_relat_1(k4_relat_1(X15))
        | ~ v1_relat_1(X15) )
      & ( k1_relat_1(X15) = k2_relat_1(k4_relat_1(X15))
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

fof(c_0_37,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(k4_relat_1(esk7_0)))
    | ~ r2_hidden(k1_funct_1(esk7_0,X1),k1_relat_1(k4_relat_1(esk7_0)))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_39,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_40,plain,(
    ! [X22] :
      ( ~ v1_relat_1(X22)
      | k5_relat_1(X22,k6_relat_1(k2_relat_1(X22))) = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

fof(c_0_41,plain,(
    ! [X13] :
      ( ~ v1_relat_1(X13)
      | v1_relat_1(k4_relat_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_42,plain,(
    ! [X41,X42,X43] :
      ( ( k1_relat_1(X42) = X41
        | X42 != k6_relat_1(X41)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( ~ r2_hidden(X43,X41)
        | k1_funct_1(X42,X43) = X43
        | X42 != k6_relat_1(X41)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( r2_hidden(esk5_2(X41,X42),X41)
        | k1_relat_1(X42) != X41
        | X42 = k6_relat_1(X41)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( k1_funct_1(X42,esk5_2(X41,X42)) != esk5_2(X41,X42)
        | k1_relat_1(X42) != X41
        | X42 = k6_relat_1(X41)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).

fof(c_0_43,plain,(
    ! [X35] :
      ( v1_relat_1(k6_relat_1(X35))
      & v1_funct_1(k6_relat_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_44,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(k4_relat_1(esk7_0)))
    | ~ r2_hidden(k1_funct_1(esk7_0,X1),k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_25])])).

fof(c_0_46,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_47,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ v1_relat_1(X21)
      | k4_relat_1(k5_relat_1(X20,X21)) = k5_relat_1(k4_relat_1(X21),k4_relat_1(X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

fof(c_0_48,plain,(
    ! [X14] :
      ( ~ v1_relat_1(X14)
      | k4_relat_1(k4_relat_1(X14)) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).

cnf(c_0_49,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_51,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( k1_relat_1(X1) = X2
    | X1 != k6_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k1_funct_1(esk7_0,X1),k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0))
    | ~ r1_tarski(k2_relat_1(k4_relat_1(esk7_0)),X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_57,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | ~ v1_relat_1(X17)
      | r1_tarski(k2_relat_1(k5_relat_1(X16,X17)),k2_relat_1(X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).

cnf(c_0_58,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( k4_relat_1(k4_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( k5_relat_1(k4_relat_1(X1),k6_relat_1(k1_relat_1(X1))) = k4_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_61,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_52]),c_0_53]),c_0_54])])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(esk7_0))
    | ~ r1_tarski(k2_relat_1(k4_relat_1(esk7_0)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_32]),c_0_24]),c_0_25])])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( k4_relat_1(k5_relat_1(k4_relat_1(X1),X2)) = k5_relat_1(k4_relat_1(X2),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_51])).

cnf(c_0_66,plain,
    ( k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X1)) = k4_relat_1(k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_54])])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(k4_relat_1(esk7_0)))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,k4_relat_1(X2))),k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_50]),c_0_51])).

cnf(c_0_70,plain,
    ( k4_relat_1(k4_relat_1(k6_relat_1(X1))) = k4_relat_1(k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_66]),c_0_54])])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(X1,k2_relat_1(k4_relat_1(esk7_0)))
    | ~ r2_hidden(esk1_2(X1,k2_relat_1(k4_relat_1(esk7_0))),k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_73,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,k4_relat_1(k6_relat_1(X2)))),X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_61]),c_0_54])])).

cnf(c_0_74,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_70]),c_0_54])])).

cnf(c_0_75,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk7_0),k2_relat_1(k4_relat_1(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,k6_relat_1(X2))),X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( k2_relat_1(k4_relat_1(esk7_0)) = k1_relat_1(esk7_0)
    | ~ r1_tarski(k2_relat_1(k4_relat_1(esk7_0)),k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_79,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(X1)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_60]),c_0_51])).

cnf(c_0_80,negated_conjecture,
    ( k2_relat_1(k4_relat_1(esk7_0)) = k1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_25])])).

cnf(c_0_81,negated_conjecture,
    ( k5_relat_1(k4_relat_1(esk7_0),k6_relat_1(k1_relat_1(esk7_0))) = k4_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_80]),c_0_35])])).

cnf(c_0_82,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk7_0)),esk7_0) = k4_relat_1(k4_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_81]),c_0_74]),c_0_54]),c_0_25])])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k2_relat_1(k4_relat_1(k4_relat_1(esk7_0))),k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_82]),c_0_25]),c_0_54])])).

cnf(c_0_84,plain,
    ( k5_relat_1(X1,k6_relat_1(k1_relat_1(k4_relat_1(X1)))) = X1
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_59]),c_0_51])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k1_relat_1(k4_relat_1(esk7_0)),k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_50]),c_0_35])])).

cnf(c_0_86,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(k6_relat_1(k1_relat_1(k4_relat_1(X1)))))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_84]),c_0_54])])).

cnf(c_0_87,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_74]),c_0_61]),c_0_54])])).

cnf(c_0_88,negated_conjecture,
    ( k1_relat_1(k4_relat_1(esk7_0)) = k2_relat_1(esk7_0)
    | ~ r1_tarski(k2_relat_1(esk7_0),k1_relat_1(k4_relat_1(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_85])).

cnf(c_0_89,plain,
    ( r1_tarski(k2_relat_1(X1),k1_relat_1(k4_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( k1_relat_1(k4_relat_1(esk7_0)) = k2_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_25])])).

fof(c_0_91,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | ~ r1_tarski(k2_relat_1(X18),k1_relat_1(X19))
      | k1_relat_1(k5_relat_1(X18,X19)) = k1_relat_1(X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).

cnf(c_0_92,negated_conjecture,
    ( k5_relat_1(k4_relat_1(k4_relat_1(esk7_0)),k6_relat_1(k2_relat_1(esk7_0))) = k4_relat_1(k4_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_90]),c_0_35])])).

cnf(c_0_93,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(X1),X2))
    | ~ v1_relat_1(k5_relat_1(k4_relat_1(X2),X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_65])).

cnf(c_0_94,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_95,plain,
    ( k4_relat_1(k5_relat_1(X1,k4_relat_1(X2))) = k5_relat_1(X2,k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_51])).

cnf(c_0_96,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k2_relat_1(esk7_0)),k4_relat_1(esk7_0)) = k4_relat_1(k4_relat_1(k4_relat_1(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_92]),c_0_74]),c_0_54]),c_0_35])])).

cnf(c_0_97,negated_conjecture,
    ( k5_relat_1(esk7_0,k6_relat_1(k2_relat_1(esk7_0))) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_90]),c_0_25])])).

cnf(c_0_98,negated_conjecture,
    ( v1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(esk7_0)),esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_81]),c_0_74]),c_0_35]),c_0_54]),c_0_25])])).

fof(c_0_99,plain,(
    ! [X23,X24,X25,X27,X28,X29,X31] :
      ( ( r2_hidden(esk2_3(X23,X24,X25),k1_relat_1(X23))
        | ~ r2_hidden(X25,X24)
        | X24 != k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( X25 = k1_funct_1(X23,esk2_3(X23,X24,X25))
        | ~ r2_hidden(X25,X24)
        | X24 != k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( ~ r2_hidden(X28,k1_relat_1(X23))
        | X27 != k1_funct_1(X23,X28)
        | r2_hidden(X27,X24)
        | X24 != k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( ~ r2_hidden(esk3_2(X23,X29),X29)
        | ~ r2_hidden(X31,k1_relat_1(X23))
        | esk3_2(X23,X29) != k1_funct_1(X23,X31)
        | X29 = k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( r2_hidden(esk4_2(X23,X29),k1_relat_1(X23))
        | r2_hidden(esk3_2(X23,X29),X29)
        | X29 = k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( esk3_2(X23,X29) = k1_funct_1(X23,esk4_2(X23,X29))
        | r2_hidden(esk3_2(X23,X29),X29)
        | X29 = k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_100,plain,
    ( k1_relat_1(k5_relat_1(X1,k4_relat_1(X2))) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_39]),c_0_51])).

cnf(c_0_101,negated_conjecture,
    ( k4_relat_1(k4_relat_1(k4_relat_1(k4_relat_1(esk7_0)))) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_74]),c_0_97]),c_0_54]),c_0_25])])).

cnf(c_0_102,negated_conjecture,
    ( v1_relat_1(k4_relat_1(k4_relat_1(esk7_0))) ),
    inference(rw,[status(thm)],[c_0_98,c_0_82])).

cnf(c_0_103,plain,
    ( X1 = k1_funct_1(X2,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

fof(c_0_104,plain,(
    ! [X38,X39,X40] :
      ( ~ v1_relat_1(X39)
      | ~ v1_funct_1(X39)
      | ~ v1_relat_1(X40)
      | ~ v1_funct_1(X40)
      | ~ r2_hidden(X38,k1_relat_1(k5_relat_1(X40,X39)))
      | k1_funct_1(k5_relat_1(X40,X39),X38) = k1_funct_1(X39,k1_funct_1(X40,X38)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).

cnf(c_0_105,plain,
    ( k1_relat_1(k5_relat_1(X1,k4_relat_1(X1))) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_100,c_0_63])).

cnf(c_0_106,negated_conjecture,
    ( k4_relat_1(k4_relat_1(esk7_0)) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_101]),c_0_102])])).

cnf(c_0_107,plain,
    ( k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_103])).

cnf(c_0_108,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_109,negated_conjecture,
    ( esk6_0 != k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),esk6_0))
    | esk6_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk7_0),esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_110,plain,
    ( k1_funct_1(k5_relat_1(X2,X1),X3) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_111,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k4_relat_1(esk7_0),esk7_0)) = k2_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_90]),c_0_35])])).

cnf(c_0_112,negated_conjecture,
    ( esk2_3(esk7_0,k2_relat_1(esk7_0),X1) = k1_funct_1(k4_relat_1(esk7_0),X1)
    | ~ r2_hidden(esk2_3(esk7_0,k2_relat_1(esk7_0),X1),k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_107]),c_0_24]),c_0_25])])).

cnf(c_0_113,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_108])).

cnf(c_0_114,negated_conjecture,
    ( k1_funct_1(esk7_0,k1_funct_1(k4_relat_1(esk7_0),esk6_0)) != esk6_0
    | k1_funct_1(k5_relat_1(k4_relat_1(esk7_0),esk7_0),esk6_0) != esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_29]),c_0_29])).

cnf(c_0_115,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k4_relat_1(esk7_0),esk7_0),X1) = k1_funct_1(esk7_0,k1_funct_1(k4_relat_1(esk7_0),X1))
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_34]),c_0_24]),c_0_35]),c_0_25])])).

cnf(c_0_116,negated_conjecture,
    ( r2_hidden(esk6_0,k2_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_117,negated_conjecture,
    ( esk2_3(esk7_0,k2_relat_1(esk7_0),X1) = k1_funct_1(k4_relat_1(esk7_0),X1)
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_24]),c_0_25])])).

cnf(c_0_118,negated_conjecture,
    ( k1_funct_1(esk7_0,k1_funct_1(k4_relat_1(esk7_0),esk6_0)) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_116])])).

cnf(c_0_119,negated_conjecture,
    ( k1_funct_1(esk7_0,k1_funct_1(k4_relat_1(esk7_0),X1)) = X1
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_117]),c_0_24]),c_0_25])])).

cnf(c_0_120,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_116])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:22:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.48  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.48  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.48  #
% 0.19/0.48  # Preprocessing time       : 0.029 s
% 0.19/0.48  # Presaturation interreduction done
% 0.19/0.48  
% 0.19/0.48  # Proof found!
% 0.19/0.48  # SZS status Theorem
% 0.19/0.48  # SZS output start CNFRefutation
% 0.19/0.48  fof(t57_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 0.19/0.48  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 0.19/0.48  fof(t56_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k1_relat_1(X2)))=>(X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))&X1=k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 0.19/0.48  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.19/0.48  fof(t12_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 0.19/0.48  fof(t37_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 0.19/0.48  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.48  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 0.19/0.48  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 0.19/0.48  fof(t34_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k6_relat_1(X1)<=>(k1_relat_1(X2)=X1&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 0.19/0.48  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.19/0.48  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.48  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 0.19/0.48  fof(involutiveness_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k4_relat_1(k4_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 0.19/0.48  fof(t45_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 0.19/0.48  fof(t46_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X1),k1_relat_1(X2))=>k1_relat_1(k5_relat_1(X1,X2))=k1_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 0.19/0.48  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.19/0.48  fof(t22_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))=>k1_funct_1(k5_relat_1(X3,X2),X1)=k1_funct_1(X2,k1_funct_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 0.19/0.48  fof(c_0_18, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1))))), inference(assume_negation,[status(cth)],[t57_funct_1])).
% 0.19/0.48  fof(c_0_19, plain, ![X33]:(~v1_relat_1(X33)|~v1_funct_1(X33)|(~v2_funct_1(X33)|k2_funct_1(X33)=k4_relat_1(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 0.19/0.48  fof(c_0_20, negated_conjecture, ((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&((v2_funct_1(esk7_0)&r2_hidden(esk6_0,k2_relat_1(esk7_0)))&(esk6_0!=k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),esk6_0))|esk6_0!=k1_funct_1(k5_relat_1(k2_funct_1(esk7_0),esk7_0),esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.19/0.48  fof(c_0_21, plain, ![X45, X46]:((X45=k1_funct_1(k2_funct_1(X46),k1_funct_1(X46,X45))|(~v2_funct_1(X46)|~r2_hidden(X45,k1_relat_1(X46)))|(~v1_relat_1(X46)|~v1_funct_1(X46)))&(X45=k1_funct_1(k5_relat_1(X46,k2_funct_1(X46)),X45)|(~v2_funct_1(X46)|~r2_hidden(X45,k1_relat_1(X46)))|(~v1_relat_1(X46)|~v1_funct_1(X46)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).
% 0.19/0.48  cnf(c_0_22, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.48  cnf(c_0_23, negated_conjecture, (v2_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.48  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.48  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.48  fof(c_0_26, plain, ![X34]:((v1_relat_1(k2_funct_1(X34))|(~v1_relat_1(X34)|~v1_funct_1(X34)))&(v1_funct_1(k2_funct_1(X34))|(~v1_relat_1(X34)|~v1_funct_1(X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.19/0.48  fof(c_0_27, plain, ![X36, X37]:(~v1_relat_1(X37)|~v1_funct_1(X37)|(~r2_hidden(X36,k1_relat_1(X37))|r2_hidden(k1_funct_1(X37,X36),k2_relat_1(X37)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).
% 0.19/0.48  cnf(c_0_28, plain, (X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))|~v2_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.48  cnf(c_0_29, negated_conjecture, (k2_funct_1(esk7_0)=k4_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])])).
% 0.19/0.48  cnf(c_0_30, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.48  cnf(c_0_31, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.48  cnf(c_0_32, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.48  cnf(c_0_33, negated_conjecture, (k1_funct_1(k4_relat_1(esk7_0),k1_funct_1(esk7_0,X1))=X1|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_23]), c_0_24]), c_0_25])])).
% 0.19/0.48  cnf(c_0_34, negated_conjecture, (v1_funct_1(k4_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_29]), c_0_24]), c_0_25])])).
% 0.19/0.48  cnf(c_0_35, negated_conjecture, (v1_relat_1(k4_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_29]), c_0_24]), c_0_25])])).
% 0.19/0.48  fof(c_0_36, plain, ![X15]:((k2_relat_1(X15)=k1_relat_1(k4_relat_1(X15))|~v1_relat_1(X15))&(k1_relat_1(X15)=k2_relat_1(k4_relat_1(X15))|~v1_relat_1(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).
% 0.19/0.48  fof(c_0_37, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.48  cnf(c_0_38, negated_conjecture, (r2_hidden(X1,k2_relat_1(k4_relat_1(esk7_0)))|~r2_hidden(k1_funct_1(esk7_0,X1),k1_relat_1(k4_relat_1(esk7_0)))|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])])).
% 0.19/0.48  cnf(c_0_39, plain, (k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.48  fof(c_0_40, plain, ![X22]:(~v1_relat_1(X22)|k5_relat_1(X22,k6_relat_1(k2_relat_1(X22)))=X22), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.19/0.48  fof(c_0_41, plain, ![X13]:(~v1_relat_1(X13)|v1_relat_1(k4_relat_1(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 0.19/0.48  fof(c_0_42, plain, ![X41, X42, X43]:(((k1_relat_1(X42)=X41|X42!=k6_relat_1(X41)|(~v1_relat_1(X42)|~v1_funct_1(X42)))&(~r2_hidden(X43,X41)|k1_funct_1(X42,X43)=X43|X42!=k6_relat_1(X41)|(~v1_relat_1(X42)|~v1_funct_1(X42))))&((r2_hidden(esk5_2(X41,X42),X41)|k1_relat_1(X42)!=X41|X42=k6_relat_1(X41)|(~v1_relat_1(X42)|~v1_funct_1(X42)))&(k1_funct_1(X42,esk5_2(X41,X42))!=esk5_2(X41,X42)|k1_relat_1(X42)!=X41|X42=k6_relat_1(X41)|(~v1_relat_1(X42)|~v1_funct_1(X42))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).
% 0.19/0.48  fof(c_0_43, plain, ![X35]:(v1_relat_1(k6_relat_1(X35))&v1_funct_1(k6_relat_1(X35))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.19/0.48  cnf(c_0_44, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.48  cnf(c_0_45, negated_conjecture, (r2_hidden(X1,k2_relat_1(k4_relat_1(esk7_0)))|~r2_hidden(k1_funct_1(esk7_0,X1),k2_relat_1(esk7_0))|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_25])])).
% 0.19/0.48  fof(c_0_46, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.48  fof(c_0_47, plain, ![X20, X21]:(~v1_relat_1(X20)|(~v1_relat_1(X21)|k4_relat_1(k5_relat_1(X20,X21))=k5_relat_1(k4_relat_1(X21),k4_relat_1(X20)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 0.19/0.48  fof(c_0_48, plain, ![X14]:(~v1_relat_1(X14)|k4_relat_1(k4_relat_1(X14))=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).
% 0.19/0.48  cnf(c_0_49, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.48  cnf(c_0_50, plain, (k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.48  cnf(c_0_51, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.48  cnf(c_0_52, plain, (k1_relat_1(X1)=X2|X1!=k6_relat_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.48  cnf(c_0_53, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.48  cnf(c_0_54, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.48  cnf(c_0_55, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(k1_funct_1(esk7_0,X1),k2_relat_1(esk7_0))|~r2_hidden(X1,k1_relat_1(esk7_0))|~r1_tarski(k2_relat_1(k4_relat_1(esk7_0)),X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.48  cnf(c_0_56, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.48  fof(c_0_57, plain, ![X16, X17]:(~v1_relat_1(X16)|(~v1_relat_1(X17)|r1_tarski(k2_relat_1(k5_relat_1(X16,X17)),k2_relat_1(X17)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).
% 0.19/0.48  cnf(c_0_58, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.48  cnf(c_0_59, plain, (k4_relat_1(k4_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.48  cnf(c_0_60, plain, (k5_relat_1(k4_relat_1(X1),k6_relat_1(k1_relat_1(X1)))=k4_relat_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.19/0.48  cnf(c_0_61, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_52]), c_0_53]), c_0_54])])).
% 0.19/0.48  cnf(c_0_62, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(esk7_0))|~r1_tarski(k2_relat_1(k4_relat_1(esk7_0)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_32]), c_0_24]), c_0_25])])).
% 0.19/0.48  cnf(c_0_63, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_56])).
% 0.19/0.48  cnf(c_0_64, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.48  cnf(c_0_65, plain, (k4_relat_1(k5_relat_1(k4_relat_1(X1),X2))=k5_relat_1(k4_relat_1(X2),X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_51])).
% 0.19/0.48  cnf(c_0_66, plain, (k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X1))=k4_relat_1(k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_54])])).
% 0.19/0.48  cnf(c_0_67, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.48  cnf(c_0_68, negated_conjecture, (r2_hidden(X1,k2_relat_1(k4_relat_1(esk7_0)))|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.48  cnf(c_0_69, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,k4_relat_1(X2))),k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_50]), c_0_51])).
% 0.19/0.48  cnf(c_0_70, plain, (k4_relat_1(k4_relat_1(k6_relat_1(X1)))=k4_relat_1(k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_66]), c_0_54])])).
% 0.19/0.48  cnf(c_0_71, negated_conjecture, (r1_tarski(X1,k2_relat_1(k4_relat_1(esk7_0)))|~r2_hidden(esk1_2(X1,k2_relat_1(k4_relat_1(esk7_0))),k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.48  cnf(c_0_72, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.48  cnf(c_0_73, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,k4_relat_1(k6_relat_1(X2)))),X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_61]), c_0_54])])).
% 0.19/0.48  cnf(c_0_74, plain, (k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_70]), c_0_54])])).
% 0.19/0.48  cnf(c_0_75, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.48  cnf(c_0_76, negated_conjecture, (r1_tarski(k1_relat_1(esk7_0),k2_relat_1(k4_relat_1(esk7_0)))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.19/0.48  cnf(c_0_77, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,k6_relat_1(X2))),X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_73, c_0_74])).
% 0.19/0.48  cnf(c_0_78, negated_conjecture, (k2_relat_1(k4_relat_1(esk7_0))=k1_relat_1(esk7_0)|~r1_tarski(k2_relat_1(k4_relat_1(esk7_0)),k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.48  cnf(c_0_79, plain, (r1_tarski(k2_relat_1(k4_relat_1(X1)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_60]), c_0_51])).
% 0.19/0.48  cnf(c_0_80, negated_conjecture, (k2_relat_1(k4_relat_1(esk7_0))=k1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_25])])).
% 0.19/0.48  cnf(c_0_81, negated_conjecture, (k5_relat_1(k4_relat_1(esk7_0),k6_relat_1(k1_relat_1(esk7_0)))=k4_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_80]), c_0_35])])).
% 0.19/0.48  cnf(c_0_82, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk7_0)),esk7_0)=k4_relat_1(k4_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_81]), c_0_74]), c_0_54]), c_0_25])])).
% 0.19/0.48  cnf(c_0_83, negated_conjecture, (r1_tarski(k2_relat_1(k4_relat_1(k4_relat_1(esk7_0))),k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_82]), c_0_25]), c_0_54])])).
% 0.19/0.48  cnf(c_0_84, plain, (k5_relat_1(X1,k6_relat_1(k1_relat_1(k4_relat_1(X1))))=X1|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_59]), c_0_51])).
% 0.19/0.48  cnf(c_0_85, negated_conjecture, (r1_tarski(k1_relat_1(k4_relat_1(esk7_0)),k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_50]), c_0_35])])).
% 0.19/0.48  cnf(c_0_86, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(k6_relat_1(k1_relat_1(k4_relat_1(X1)))))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_84]), c_0_54])])).
% 0.19/0.48  cnf(c_0_87, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_74]), c_0_61]), c_0_54])])).
% 0.19/0.48  cnf(c_0_88, negated_conjecture, (k1_relat_1(k4_relat_1(esk7_0))=k2_relat_1(esk7_0)|~r1_tarski(k2_relat_1(esk7_0),k1_relat_1(k4_relat_1(esk7_0)))), inference(spm,[status(thm)],[c_0_75, c_0_85])).
% 0.19/0.48  cnf(c_0_89, plain, (r1_tarski(k2_relat_1(X1),k1_relat_1(k4_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_86, c_0_87])).
% 0.19/0.48  cnf(c_0_90, negated_conjecture, (k1_relat_1(k4_relat_1(esk7_0))=k2_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_25])])).
% 0.19/0.48  fof(c_0_91, plain, ![X18, X19]:(~v1_relat_1(X18)|(~v1_relat_1(X19)|(~r1_tarski(k2_relat_1(X18),k1_relat_1(X19))|k1_relat_1(k5_relat_1(X18,X19))=k1_relat_1(X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).
% 0.19/0.48  cnf(c_0_92, negated_conjecture, (k5_relat_1(k4_relat_1(k4_relat_1(esk7_0)),k6_relat_1(k2_relat_1(esk7_0)))=k4_relat_1(k4_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_90]), c_0_35])])).
% 0.19/0.48  cnf(c_0_93, plain, (v1_relat_1(k5_relat_1(k4_relat_1(X1),X2))|~v1_relat_1(k5_relat_1(k4_relat_1(X2),X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_51, c_0_65])).
% 0.19/0.48  cnf(c_0_94, plain, (k1_relat_1(k5_relat_1(X1,X2))=k1_relat_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X1),k1_relat_1(X2))), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.19/0.48  cnf(c_0_95, plain, (k4_relat_1(k5_relat_1(X1,k4_relat_1(X2)))=k5_relat_1(X2,k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_51])).
% 0.19/0.48  cnf(c_0_96, negated_conjecture, (k5_relat_1(k6_relat_1(k2_relat_1(esk7_0)),k4_relat_1(esk7_0))=k4_relat_1(k4_relat_1(k4_relat_1(esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_92]), c_0_74]), c_0_54]), c_0_35])])).
% 0.19/0.48  cnf(c_0_97, negated_conjecture, (k5_relat_1(esk7_0,k6_relat_1(k2_relat_1(esk7_0)))=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_90]), c_0_25])])).
% 0.19/0.48  cnf(c_0_98, negated_conjecture, (v1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(esk7_0)),esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_81]), c_0_74]), c_0_35]), c_0_54]), c_0_25])])).
% 0.19/0.48  fof(c_0_99, plain, ![X23, X24, X25, X27, X28, X29, X31]:((((r2_hidden(esk2_3(X23,X24,X25),k1_relat_1(X23))|~r2_hidden(X25,X24)|X24!=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(X25=k1_funct_1(X23,esk2_3(X23,X24,X25))|~r2_hidden(X25,X24)|X24!=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23))))&(~r2_hidden(X28,k1_relat_1(X23))|X27!=k1_funct_1(X23,X28)|r2_hidden(X27,X24)|X24!=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23))))&((~r2_hidden(esk3_2(X23,X29),X29)|(~r2_hidden(X31,k1_relat_1(X23))|esk3_2(X23,X29)!=k1_funct_1(X23,X31))|X29=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&((r2_hidden(esk4_2(X23,X29),k1_relat_1(X23))|r2_hidden(esk3_2(X23,X29),X29)|X29=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(esk3_2(X23,X29)=k1_funct_1(X23,esk4_2(X23,X29))|r2_hidden(esk3_2(X23,X29),X29)|X29=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.19/0.48  cnf(c_0_100, plain, (k1_relat_1(k5_relat_1(X1,k4_relat_1(X2)))=k1_relat_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X1),k2_relat_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_39]), c_0_51])).
% 0.19/0.48  cnf(c_0_101, negated_conjecture, (k4_relat_1(k4_relat_1(k4_relat_1(k4_relat_1(esk7_0))))=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_74]), c_0_97]), c_0_54]), c_0_25])])).
% 0.19/0.48  cnf(c_0_102, negated_conjecture, (v1_relat_1(k4_relat_1(k4_relat_1(esk7_0)))), inference(rw,[status(thm)],[c_0_98, c_0_82])).
% 0.19/0.48  cnf(c_0_103, plain, (X1=k1_funct_1(X2,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.19/0.48  fof(c_0_104, plain, ![X38, X39, X40]:(~v1_relat_1(X39)|~v1_funct_1(X39)|(~v1_relat_1(X40)|~v1_funct_1(X40)|(~r2_hidden(X38,k1_relat_1(k5_relat_1(X40,X39)))|k1_funct_1(k5_relat_1(X40,X39),X38)=k1_funct_1(X39,k1_funct_1(X40,X38))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).
% 0.19/0.48  cnf(c_0_105, plain, (k1_relat_1(k5_relat_1(X1,k4_relat_1(X1)))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_100, c_0_63])).
% 0.19/0.48  cnf(c_0_106, negated_conjecture, (k4_relat_1(k4_relat_1(esk7_0))=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_101]), c_0_102])])).
% 0.19/0.48  cnf(c_0_107, plain, (k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_103])).
% 0.19/0.48  cnf(c_0_108, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.19/0.48  cnf(c_0_109, negated_conjecture, (esk6_0!=k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),esk6_0))|esk6_0!=k1_funct_1(k5_relat_1(k2_funct_1(esk7_0),esk7_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.48  cnf(c_0_110, plain, (k1_funct_1(k5_relat_1(X2,X1),X3)=k1_funct_1(X1,k1_funct_1(X2,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_104])).
% 0.19/0.48  cnf(c_0_111, negated_conjecture, (k1_relat_1(k5_relat_1(k4_relat_1(esk7_0),esk7_0))=k2_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_90]), c_0_35])])).
% 0.19/0.48  cnf(c_0_112, negated_conjecture, (esk2_3(esk7_0,k2_relat_1(esk7_0),X1)=k1_funct_1(k4_relat_1(esk7_0),X1)|~r2_hidden(esk2_3(esk7_0,k2_relat_1(esk7_0),X1),k1_relat_1(esk7_0))|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_107]), c_0_24]), c_0_25])])).
% 0.19/0.48  cnf(c_0_113, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_108])).
% 0.19/0.48  cnf(c_0_114, negated_conjecture, (k1_funct_1(esk7_0,k1_funct_1(k4_relat_1(esk7_0),esk6_0))!=esk6_0|k1_funct_1(k5_relat_1(k4_relat_1(esk7_0),esk7_0),esk6_0)!=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_29]), c_0_29])).
% 0.19/0.48  cnf(c_0_115, negated_conjecture, (k1_funct_1(k5_relat_1(k4_relat_1(esk7_0),esk7_0),X1)=k1_funct_1(esk7_0,k1_funct_1(k4_relat_1(esk7_0),X1))|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_34]), c_0_24]), c_0_35]), c_0_25])])).
% 0.19/0.48  cnf(c_0_116, negated_conjecture, (r2_hidden(esk6_0,k2_relat_1(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.48  cnf(c_0_117, negated_conjecture, (esk2_3(esk7_0,k2_relat_1(esk7_0),X1)=k1_funct_1(k4_relat_1(esk7_0),X1)|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_24]), c_0_25])])).
% 0.19/0.48  cnf(c_0_118, negated_conjecture, (k1_funct_1(esk7_0,k1_funct_1(k4_relat_1(esk7_0),esk6_0))!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_116])])).
% 0.19/0.48  cnf(c_0_119, negated_conjecture, (k1_funct_1(esk7_0,k1_funct_1(k4_relat_1(esk7_0),X1))=X1|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_117]), c_0_24]), c_0_25])])).
% 0.19/0.48  cnf(c_0_120, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_116])]), ['proof']).
% 0.19/0.48  # SZS output end CNFRefutation
% 0.19/0.48  # Proof object total steps             : 121
% 0.19/0.48  # Proof object clause steps            : 84
% 0.19/0.48  # Proof object formula steps           : 37
% 0.19/0.48  # Proof object conjectures             : 42
% 0.19/0.48  # Proof object clause conjectures      : 39
% 0.19/0.48  # Proof object formula conjectures     : 3
% 0.19/0.48  # Proof object initial clauses used    : 29
% 0.19/0.48  # Proof object initial formulas used   : 18
% 0.19/0.48  # Proof object generating inferences   : 47
% 0.19/0.48  # Proof object simplifying inferences  : 110
% 0.19/0.48  # Training examples: 0 positive, 0 negative
% 0.19/0.48  # Parsed axioms                        : 18
% 0.19/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.48  # Initial clauses                      : 38
% 0.19/0.48  # Removed in clause preprocessing      : 0
% 0.19/0.48  # Initial clauses in saturation        : 38
% 0.19/0.48  # Processed clauses                    : 860
% 0.19/0.48  # ...of these trivial                  : 16
% 0.19/0.48  # ...subsumed                          : 393
% 0.19/0.48  # ...remaining for further processing  : 451
% 0.19/0.48  # Other redundant clauses eliminated   : 10
% 0.19/0.48  # Clauses deleted for lack of memory   : 0
% 0.19/0.48  # Backward-subsumed                    : 8
% 0.19/0.48  # Backward-rewritten                   : 73
% 0.19/0.48  # Generated clauses                    : 4600
% 0.19/0.48  # ...of the previous two non-trivial   : 3903
% 0.19/0.48  # Contextual simplify-reflections      : 51
% 0.19/0.48  # Paramodulations                      : 4591
% 0.19/0.48  # Factorizations                       : 0
% 0.19/0.48  # Equation resolutions                 : 10
% 0.19/0.48  # Propositional unsat checks           : 0
% 0.19/0.48  #    Propositional check models        : 0
% 0.19/0.48  #    Propositional check unsatisfiable : 0
% 0.19/0.48  #    Propositional clauses             : 0
% 0.19/0.48  #    Propositional clauses after purity: 0
% 0.19/0.48  #    Propositional unsat core size     : 0
% 0.19/0.48  #    Propositional preprocessing time  : 0.000
% 0.19/0.48  #    Propositional encoding time       : 0.000
% 0.19/0.48  #    Propositional solver time         : 0.000
% 0.19/0.48  #    Success case prop preproc time    : 0.000
% 0.19/0.48  #    Success case prop encoding time   : 0.000
% 0.19/0.48  #    Success case prop solver time     : 0.000
% 0.19/0.48  # Current number of processed clauses  : 325
% 0.19/0.48  #    Positive orientable unit clauses  : 40
% 0.19/0.48  #    Positive unorientable unit clauses: 0
% 0.19/0.48  #    Negative unit clauses             : 1
% 0.19/0.48  #    Non-unit-clauses                  : 284
% 0.19/0.48  # Current number of unprocessed clauses: 3062
% 0.19/0.48  # ...number of literals in the above   : 13158
% 0.19/0.48  # Current number of archived formulas  : 0
% 0.19/0.48  # Current number of archived clauses   : 117
% 0.19/0.48  # Clause-clause subsumption calls (NU) : 12875
% 0.19/0.48  # Rec. Clause-clause subsumption calls : 9256
% 0.19/0.48  # Non-unit clause-clause subsumptions  : 449
% 0.19/0.48  # Unit Clause-clause subsumption calls : 200
% 0.19/0.48  # Rewrite failures with RHS unbound    : 0
% 0.19/0.48  # BW rewrite match attempts            : 107
% 0.19/0.48  # BW rewrite match successes           : 32
% 0.19/0.48  # Condensation attempts                : 0
% 0.19/0.48  # Condensation successes               : 0
% 0.19/0.48  # Termbank termtop insertions          : 113559
% 0.19/0.48  
% 0.19/0.48  # -------------------------------------------------
% 0.19/0.48  # User time                : 0.135 s
% 0.19/0.48  # System time              : 0.009 s
% 0.19/0.48  # Total time               : 0.145 s
% 0.19/0.48  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
