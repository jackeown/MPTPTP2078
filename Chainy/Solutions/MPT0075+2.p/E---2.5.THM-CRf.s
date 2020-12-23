%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0075+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:35 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   48 (  62 expanded)
%              Number of clauses        :   26 (  27 expanded)
%              Number of leaves         :   11 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   96 ( 141 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t68_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ~ ( r1_tarski(X3,X1)
          & r1_tarski(X3,X2)
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',symmetry_r1_xboole_0)).

fof(fc4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X1)
     => ~ v1_xboole_0(k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',fc1_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t7_xboole_0)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ~ ( r1_tarski(X3,X1)
            & r1_tarski(X3,X2)
            & r1_xboole_0(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t68_xboole_1])).

fof(c_0_12,plain,(
    ! [X82,X83,X85,X86,X87] :
      ( ( r1_xboole_0(X82,X83)
        | r2_hidden(esk11_2(X82,X83),k3_xboole_0(X82,X83)) )
      & ( ~ r2_hidden(X87,k3_xboole_0(X85,X86))
        | ~ r1_xboole_0(X85,X86) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_13,plain,(
    ! [X222,X223] : k4_xboole_0(X222,k4_xboole_0(X222,X223)) = k3_xboole_0(X222,X223) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_14,plain,(
    ! [X265,X266,X267] :
      ( ~ r1_tarski(X265,X266)
      | ~ r1_xboole_0(X266,X267)
      | r1_xboole_0(X265,X267) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_15,negated_conjecture,
    ( ~ v1_xboole_0(esk18_0)
    & r1_tarski(esk18_0,esk16_0)
    & r1_tarski(esk18_0,esk17_0)
    & r1_xboole_0(esk16_0,esk17_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_16,plain,(
    ! [X64,X65] :
      ( ~ r1_xboole_0(X64,X65)
      | r1_xboole_0(X65,X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_17,plain,(
    ! [X98,X99] :
      ( v1_xboole_0(X98)
      | ~ v1_xboole_0(k2_xboole_0(X98,X99)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_xboole_0])])])).

fof(c_0_18,plain,(
    ! [X116,X117] :
      ( ~ r1_tarski(X116,X117)
      | k2_xboole_0(X116,X117) = X117 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_19,plain,(
    ! [X102,X103] :
      ( ( k4_xboole_0(X102,X103) != k1_xboole_0
        | r1_tarski(X102,X103) )
      & ( ~ r1_tarski(X102,X103)
        | k4_xboole_0(X102,X103) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_20,plain,(
    ! [X200] : k4_xboole_0(X200,k1_xboole_0) = X200 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk18_0,esk17_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( r1_xboole_0(esk16_0,esk17_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( r1_xboole_0(esk18_0,X1)
    | ~ r1_xboole_0(esk17_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( r1_xboole_0(esk17_0,esk16_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_38,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( r1_xboole_0(esk18_0,esk16_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk18_0,esk16_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_41,plain,(
    ! [X94] :
      ( X94 = k1_xboole_0
      | r2_hidden(esk13_1(X94),X94) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_xboole_0(esk18_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X1)
    | X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(X1,esk18_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk13_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( esk18_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
