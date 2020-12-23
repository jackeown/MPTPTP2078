%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0077+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:35 EST 2020

% Result     : Theorem 43.42s
% Output     : CNFRefutation 43.42s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 183 expanded)
%              Number of clauses        :   41 (  82 expanded)
%              Number of leaves         :   14 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :  132 ( 406 expanded)
%              Number of equality atoms :   36 (  72 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t70_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',symmetry_r1_xboole_0)).

fof(t53_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',t4_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(c_0_14,plain,(
    ! [X265,X266,X267] :
      ( ~ r1_tarski(X265,X266)
      | ~ r1_xboole_0(X266,X267)
      | r1_xboole_0(X265,X267) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_15,plain,(
    ! [X290,X291] : r1_tarski(X290,k2_xboole_0(X290,X291)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
            & r1_xboole_0(X1,X2)
            & r1_xboole_0(X1,X3) )
        & ~ ( ~ ( r1_xboole_0(X1,X2)
                & r1_xboole_0(X1,X3) )
            & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t70_xboole_1])).

fof(c_0_17,plain,(
    ! [X234,X235] : k2_xboole_0(k3_xboole_0(X234,X235),k4_xboole_0(X234,X235)) = X234 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_18,plain,(
    ! [X222,X223] : k4_xboole_0(X222,k4_xboole_0(X222,X223)) = k3_xboole_0(X222,X223) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k2_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_22,plain,(
    ! [X64,X65] :
      ( ~ r1_xboole_0(X64,X65)
      | r1_xboole_0(X65,X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_23,negated_conjecture,
    ( ( ~ r1_xboole_0(esk16_0,esk17_0)
      | ~ r1_xboole_0(esk16_0,esk18_0)
      | ~ r1_xboole_0(esk16_0,k2_xboole_0(esk17_0,esk18_0)) )
    & ( r1_xboole_0(esk16_0,k2_xboole_0(esk17_0,esk18_0))
      | ~ r1_xboole_0(esk16_0,k2_xboole_0(esk17_0,esk18_0)) )
    & ( ~ r1_xboole_0(esk16_0,esk17_0)
      | ~ r1_xboole_0(esk16_0,esk18_0)
      | r1_xboole_0(esk16_0,esk17_0) )
    & ( r1_xboole_0(esk16_0,k2_xboole_0(esk17_0,esk18_0))
      | r1_xboole_0(esk16_0,esk17_0) )
    & ( ~ r1_xboole_0(esk16_0,esk17_0)
      | ~ r1_xboole_0(esk16_0,esk18_0)
      | r1_xboole_0(esk16_0,esk18_0) )
    & ( r1_xboole_0(esk16_0,k2_xboole_0(esk17_0,esk18_0))
      | r1_xboole_0(esk16_0,esk18_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])).

fof(c_0_24,plain,(
    ! [X239,X240,X241] : k4_xboole_0(X239,k2_xboole_0(X240,X241)) = k3_xboole_0(k4_xboole_0(X239,X240),k4_xboole_0(X239,X241)) ),
    inference(variable_rename,[status(thm)],[t53_xboole_1])).

fof(c_0_25,plain,(
    ! [X54,X55] :
      ( ( ~ r1_xboole_0(X54,X55)
        | k3_xboole_0(X54,X55) = k1_xboole_0 )
      & ( k3_xboole_0(X54,X55) != k1_xboole_0
        | r1_xboole_0(X54,X55) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_28,plain,(
    ! [X198,X199] : k2_xboole_0(X198,k4_xboole_0(X199,X198)) = k2_xboole_0(X198,X199) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( r1_xboole_0(esk16_0,k2_xboole_0(esk17_0,esk18_0))
    | r1_xboole_0(esk16_0,esk18_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( r1_xboole_0(esk16_0,k2_xboole_0(esk17_0,esk18_0))
    | r1_xboole_0(esk16_0,esk17_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_34,plain,(
    ! [X82,X83,X85,X86,X87] :
      ( ( r1_xboole_0(X82,X83)
        | r2_hidden(esk11_2(X82,X83),k3_xboole_0(X82,X83)) )
      & ( ~ r2_hidden(X87,k3_xboole_0(X85,X86))
        | ~ r1_xboole_0(X85,X86) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_36,plain,(
    ! [X204,X205,X206] : k4_xboole_0(k4_xboole_0(X204,X205),X206) = k4_xboole_0(X204,k2_xboole_0(X205,X206)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_38,plain,(
    ! [X139] : k2_xboole_0(X139,k1_xboole_0) = X139 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_39,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk17_0,esk18_0),esk16_0)
    | r1_xboole_0(esk16_0,esk18_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk17_0,esk18_0),esk16_0)
    | r1_xboole_0(esk16_0,esk17_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_33])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_27])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_27])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_30]),c_0_40]),c_0_30])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(esk18_0,esk16_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_31])).

fof(c_0_51,plain,(
    ! [X218,X219] : k4_xboole_0(X218,k2_xboole_0(X218,X219)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_52,negated_conjecture,
    ( r1_xboole_0(esk17_0,esk16_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_43]),c_0_31])).

cnf(c_0_53,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_27])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))))) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_46])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_47]),c_0_48]),c_0_30]),c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(esk16_0,esk18_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_50])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_xboole_0(esk16_0,esk17_0)
    | ~ r1_xboole_0(esk16_0,esk18_0)
    | ~ r1_xboole_0(esk16_0,k2_xboole_0(esk17_0,esk18_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_59,negated_conjecture,
    ( r1_xboole_0(esk16_0,esk17_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_52])).

cnf(c_0_60,plain,
    ( ~ r1_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))))
    | ~ r2_hidden(X4,k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(esk16_0,esk18_0) = esk16_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_30])).

cnf(c_0_63,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk11_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_xboole_0(esk16_0,k2_xboole_0(esk17_0,esk18_0))
    | ~ r1_xboole_0(esk16_0,esk18_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_xboole_0(esk16_0,X1)
    | ~ r2_hidden(X2,k4_xboole_0(esk16_0,k4_xboole_0(esk16_0,k2_xboole_0(X1,esk18_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_48])).

cnf(c_0_66,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk11_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_63,c_0_27])).

cnf(c_0_67,negated_conjecture,
    ( ~ r1_xboole_0(esk16_0,k2_xboole_0(esk17_0,esk18_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_56])])).

cnf(c_0_68,negated_conjecture,
    ( r1_xboole_0(esk16_0,k2_xboole_0(X1,esk18_0))
    | ~ r1_xboole_0(esk16_0,X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_59])]),
    [proof]).
%------------------------------------------------------------------------------
