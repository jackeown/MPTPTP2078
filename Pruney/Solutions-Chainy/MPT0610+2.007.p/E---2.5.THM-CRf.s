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
% DateTime   : Thu Dec  3 10:52:36 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 244 expanded)
%              Number of clauses        :   55 ( 109 expanded)
%              Number of leaves         :   16 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  205 ( 616 expanded)
%              Number of equality atoms :   42 (  84 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    7 (   2 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t74_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,k3_xboole_0(X2,X3))
        & r1_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

fof(t76_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t214_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))
           => r1_xboole_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t88_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(t14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t196_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( ( k1_relat_1(X1) = k1_xboole_0
              & k1_relat_1(X2) = k1_xboole_0 )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t196_relat_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t90_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).

fof(c_0_16,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_xboole_0(X8,X9) )
      & ( r2_hidden(esk1_2(X8,X9),X9)
        | r1_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_20,plain,(
    ! [X31,X32,X33] :
      ( r1_xboole_0(X31,k3_xboole_0(X32,X33))
      | ~ r1_xboole_0(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_xboole_1])])])).

cnf(c_0_21,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_22,plain,(
    ! [X34,X35,X36] :
      ( ~ r1_xboole_0(X34,X35)
      | r1_xboole_0(k3_xboole_0(X36,X34),k3_xboole_0(X36,X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_xboole_1])])).

fof(c_0_23,plain,(
    ! [X23] : r1_xboole_0(X23,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_24,plain,(
    ! [X52,X53] :
      ( ~ v1_relat_1(X52)
      | v1_relat_1(k3_xboole_0(X52,X53)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

fof(c_0_25,plain,(
    ! [X4,X5] :
      ( ( ~ r1_xboole_0(X4,X5)
        | k3_xboole_0(X4,X5) = k1_xboole_0 )
      & ( k3_xboole_0(X4,X5) != k1_xboole_0
        | r1_xboole_0(X4,X5) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_29,plain,
    ( r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))
             => r1_xboole_0(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t214_relat_1])).

fof(c_0_34,plain,(
    ! [X24] :
      ( ( r1_xboole_0(X24,X24)
        | X24 != k1_xboole_0 )
      & ( X24 = k1_xboole_0
        | ~ r1_xboole_0(X24,X24) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

fof(c_0_35,plain,(
    ! [X45,X46,X47] :
      ( ~ r1_tarski(X45,X46)
      | r1_xboole_0(X45,k4_xboole_0(X47,X46)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

cnf(c_0_36,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X3,X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_30])).

cnf(c_0_39,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_40,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & r1_xboole_0(k1_relat_1(esk3_0),k1_relat_1(esk4_0))
    & ~ r1_xboole_0(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_43,plain,(
    ! [X48,X49] :
      ( ~ r1_xboole_0(X48,X49)
      | k4_xboole_0(k2_xboole_0(X48,X49),X49) = X48 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).

fof(c_0_44,plain,(
    ! [X56,X57] :
      ( ~ v1_relat_1(X56)
      | ~ v1_relat_1(X57)
      | r1_tarski(k1_relat_1(k3_xboole_0(X56,X57)),k3_xboole_0(k1_relat_1(X56),k1_relat_1(X57))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relat_1])])])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(k3_xboole_0(X2,X3),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_36])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_30])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_30])).

fof(c_0_53,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,X21)
      | ~ r1_xboole_0(X21,X22)
      | r1_xboole_0(X20,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k1_xboole_0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_32])).

cnf(c_0_58,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk3_0),k1_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_59,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_52])).

cnf(c_0_60,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k3_xboole_0(k1_relat_1(X1),k1_relat_1(k1_xboole_0)))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_54]),c_0_55])])).

fof(c_0_62,plain,(
    ! [X58,X59] :
      ( ~ v1_relat_1(X58)
      | ~ v1_relat_1(X59)
      | k1_relat_1(X58) != k1_xboole_0
      | k1_relat_1(X59) != k1_xboole_0
      | X58 = X59 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t196_relat_1])])])).

cnf(c_0_63,plain,
    ( k1_relat_1(k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_30])])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk4_0),k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_66,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k3_xboole_0(k1_relat_1(k1_xboole_0),k1_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_59]),c_0_55])])).

cnf(c_0_67,plain,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),X1)
    | ~ v1_relat_1(X2)
    | ~ r1_xboole_0(k3_xboole_0(k1_relat_1(X2),k1_relat_1(k1_xboole_0)),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

fof(c_0_68,plain,(
    ! [X43,X44] :
      ( ( ~ r1_xboole_0(X43,X44)
        | k4_xboole_0(X43,X44) = X43 )
      & ( k4_xboole_0(X43,X44) != X43
        | r1_xboole_0(X43,X44) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_69,plain,
    ( X1 = X2
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_relat_1(X1) != k1_xboole_0
    | k1_relat_1(X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( k1_relat_1(k3_xboole_0(esk4_0,esk3_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_48])])).

cnf(c_0_71,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k1_relat_1(k1_xboole_0),k3_xboole_0(k1_relat_1(k1_xboole_0),k1_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_66])).

cnf(c_0_72,plain,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),X1)
    | ~ v1_relat_1(X2)
    | ~ r1_xboole_0(X1,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_36])).

cnf(c_0_73,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

fof(c_0_74,plain,(
    ! [X50,X51] : r1_xboole_0(k4_xboole_0(X50,k3_xboole_0(X50,X51)),X51) ),
    inference(variable_rename,[status(thm)],[t90_xboole_1])).

cnf(c_0_75,negated_conjecture,
    ( X1 = k3_xboole_0(esk4_0,esk3_0)
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(k3_xboole_0(esk4_0,esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k1_relat_1(k1_xboole_0),k1_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_32]),c_0_30])])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_64]),c_0_65])])).

cnf(c_0_78,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(k2_xboole_0(X1,X2),X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_50])).

cnf(c_0_79,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( X1 = k3_xboole_0(esk4_0,esk3_0)
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_31]),c_0_48])])).

cnf(c_0_81,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_48])])).

cnf(c_0_82,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_30]),c_0_30])])).

cnf(c_0_83,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_55])])).

cnf(c_0_85,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_82]),c_0_30])])).

cnf(c_0_86,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85]),c_0_86]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n015.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 09:58:23 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.47  # AutoSched0-Mode selected heuristic G_E___208_C12_02_nc_F1_SE_CS_SP_PS_S06DN
% 0.20/0.47  # and selection function SelectNewComplexAHPExceptUniqMaxHorn.
% 0.20/0.47  #
% 0.20/0.47  # Preprocessing time       : 0.028 s
% 0.20/0.47  # Presaturation interreduction done
% 0.20/0.47  
% 0.20/0.47  # Proof found!
% 0.20/0.47  # SZS status Theorem
% 0.20/0.47  # SZS output start CNFRefutation
% 0.20/0.47  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.47  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.47  fof(t74_xboole_1, axiom, ![X1, X2, X3]:~((~(r1_xboole_0(X1,k3_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 0.20/0.47  fof(t76_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_xboole_1)).
% 0.20/0.47  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.20/0.47  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.20/0.47  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.20/0.47  fof(t214_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=>r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t214_relat_1)).
% 0.20/0.47  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.20/0.47  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.20/0.47  fof(t88_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 0.20/0.47  fof(t14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relat_1)).
% 0.20/0.47  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.20/0.47  fof(t196_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>((k1_relat_1(X1)=k1_xboole_0&k1_relat_1(X2)=k1_xboole_0)=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t196_relat_1)).
% 0.20/0.47  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.47  fof(t90_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_xboole_1)).
% 0.20/0.47  fof(c_0_16, plain, ![X8, X9, X11, X12, X13]:(((r2_hidden(esk1_2(X8,X9),X8)|r1_xboole_0(X8,X9))&(r2_hidden(esk1_2(X8,X9),X9)|r1_xboole_0(X8,X9)))&(~r2_hidden(X13,X11)|~r2_hidden(X13,X12)|~r1_xboole_0(X11,X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.47  cnf(c_0_17, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.47  cnf(c_0_18, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.47  fof(c_0_19, plain, ![X6, X7]:(~r1_xboole_0(X6,X7)|r1_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.47  fof(c_0_20, plain, ![X31, X32, X33]:(r1_xboole_0(X31,k3_xboole_0(X32,X33))|~r1_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_xboole_1])])])).
% 0.20/0.47  cnf(c_0_21, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.47  fof(c_0_22, plain, ![X34, X35, X36]:(~r1_xboole_0(X34,X35)|r1_xboole_0(k3_xboole_0(X36,X34),k3_xboole_0(X36,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_xboole_1])])).
% 0.20/0.47  fof(c_0_23, plain, ![X23]:r1_xboole_0(X23,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.20/0.47  fof(c_0_24, plain, ![X52, X53]:(~v1_relat_1(X52)|v1_relat_1(k3_xboole_0(X52,X53))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.20/0.47  fof(c_0_25, plain, ![X4, X5]:((~r1_xboole_0(X4,X5)|k3_xboole_0(X4,X5)=k1_xboole_0)&(k3_xboole_0(X4,X5)!=k1_xboole_0|r1_xboole_0(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.20/0.47  cnf(c_0_26, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.47  cnf(c_0_27, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.47  cnf(c_0_28, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_21, c_0_18])).
% 0.20/0.47  cnf(c_0_29, plain, (r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  cnf(c_0_30, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.47  cnf(c_0_31, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.47  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.47  fof(c_0_33, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=>r1_xboole_0(X1,X2))))), inference(assume_negation,[status(cth)],[t214_relat_1])).
% 0.20/0.47  fof(c_0_34, plain, ![X24]:((r1_xboole_0(X24,X24)|X24!=k1_xboole_0)&(X24=k1_xboole_0|~r1_xboole_0(X24,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.20/0.47  fof(c_0_35, plain, ![X45, X46, X47]:(~r1_tarski(X45,X46)|r1_xboole_0(X45,k4_xboole_0(X47,X46))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.20/0.47  cnf(c_0_36, plain, (r1_xboole_0(k3_xboole_0(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.47  cnf(c_0_37, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X3,X3)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.47  cnf(c_0_38, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_26, c_0_30])).
% 0.20/0.47  cnf(c_0_39, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.47  fof(c_0_40, negated_conjecture, (v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&(r1_xboole_0(k1_relat_1(esk3_0),k1_relat_1(esk4_0))&~r1_xboole_0(esk3_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).
% 0.20/0.47  cnf(c_0_41, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.47  cnf(c_0_42, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.47  fof(c_0_43, plain, ![X48, X49]:(~r1_xboole_0(X48,X49)|k4_xboole_0(k2_xboole_0(X48,X49),X49)=X48), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).
% 0.20/0.47  fof(c_0_44, plain, ![X56, X57]:(~v1_relat_1(X56)|(~v1_relat_1(X57)|r1_tarski(k1_relat_1(k3_xboole_0(X56,X57)),k3_xboole_0(k1_relat_1(X56),k1_relat_1(X57))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relat_1])])])).
% 0.20/0.47  cnf(c_0_45, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(k3_xboole_0(X2,X3),X2)), inference(spm,[status(thm)],[c_0_28, c_0_36])).
% 0.20/0.47  cnf(c_0_46, plain, (r1_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.47  cnf(c_0_47, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_30])).
% 0.20/0.47  cnf(c_0_48, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.47  cnf(c_0_49, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(k4_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.47  cnf(c_0_50, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.47  cnf(c_0_51, plain, (r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.47  cnf(c_0_52, plain, (r1_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_45, c_0_30])).
% 0.20/0.47  fof(c_0_53, plain, ![X20, X21, X22]:(~r1_tarski(X20,X21)|~r1_xboole_0(X21,X22)|r1_xboole_0(X20,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.20/0.47  cnf(c_0_54, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_46])).
% 0.20/0.47  cnf(c_0_55, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.47  cnf(c_0_56, plain, (X1=k1_xboole_0|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.47  cnf(c_0_57, plain, (r1_tarski(k1_relat_1(k3_xboole_0(X1,X2)),k1_xboole_0)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_51, c_0_32])).
% 0.20/0.47  cnf(c_0_58, negated_conjecture, (r1_xboole_0(k1_relat_1(esk3_0),k1_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.47  cnf(c_0_59, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_52])).
% 0.20/0.47  cnf(c_0_60, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.47  cnf(c_0_61, plain, (r1_tarski(k1_relat_1(k1_xboole_0),k3_xboole_0(k1_relat_1(X1),k1_relat_1(k1_xboole_0)))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_54]), c_0_55])])).
% 0.20/0.47  fof(c_0_62, plain, ![X58, X59]:(~v1_relat_1(X58)|(~v1_relat_1(X59)|(k1_relat_1(X58)!=k1_xboole_0|k1_relat_1(X59)!=k1_xboole_0|X58=X59))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t196_relat_1])])])).
% 0.20/0.47  cnf(c_0_63, plain, (k1_relat_1(k3_xboole_0(X1,X2))=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_xboole_0(k1_relat_1(X1),k1_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_30])])).
% 0.20/0.47  cnf(c_0_64, negated_conjecture, (r1_xboole_0(k1_relat_1(esk4_0),k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_26, c_0_58])).
% 0.20/0.47  cnf(c_0_65, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.47  cnf(c_0_66, plain, (r1_tarski(k1_relat_1(k1_xboole_0),k3_xboole_0(k1_relat_1(k1_xboole_0),k1_relat_1(X1)))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_59]), c_0_55])])).
% 0.20/0.47  cnf(c_0_67, plain, (r1_xboole_0(k1_relat_1(k1_xboole_0),X1)|~v1_relat_1(X2)|~r1_xboole_0(k3_xboole_0(k1_relat_1(X2),k1_relat_1(k1_xboole_0)),X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.47  fof(c_0_68, plain, ![X43, X44]:((~r1_xboole_0(X43,X44)|k4_xboole_0(X43,X44)=X43)&(k4_xboole_0(X43,X44)!=X43|r1_xboole_0(X43,X44))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.20/0.47  cnf(c_0_69, plain, (X1=X2|~v1_relat_1(X1)|~v1_relat_1(X2)|k1_relat_1(X1)!=k1_xboole_0|k1_relat_1(X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.47  cnf(c_0_70, negated_conjecture, (k1_relat_1(k3_xboole_0(esk4_0,esk3_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_48])])).
% 0.20/0.47  cnf(c_0_71, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(k1_relat_1(k1_xboole_0),k3_xboole_0(k1_relat_1(k1_xboole_0),k1_relat_1(X1)))), inference(spm,[status(thm)],[c_0_56, c_0_66])).
% 0.20/0.47  cnf(c_0_72, plain, (r1_xboole_0(k1_relat_1(k1_xboole_0),X1)|~v1_relat_1(X2)|~r1_xboole_0(X1,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_67, c_0_36])).
% 0.20/0.47  cnf(c_0_73, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.47  fof(c_0_74, plain, ![X50, X51]:r1_xboole_0(k4_xboole_0(X50,k3_xboole_0(X50,X51)),X51), inference(variable_rename,[status(thm)],[t90_xboole_1])).
% 0.20/0.47  cnf(c_0_75, negated_conjecture, (X1=k3_xboole_0(esk4_0,esk3_0)|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(k3_xboole_0(esk4_0,esk3_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.47  cnf(c_0_76, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(k1_relat_1(k1_xboole_0),k1_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_32]), c_0_30])])).
% 0.20/0.47  cnf(c_0_77, negated_conjecture, (r1_xboole_0(k1_relat_1(k1_xboole_0),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_64]), c_0_65])])).
% 0.20/0.47  cnf(c_0_78, plain, (k2_xboole_0(X1,X2)=X1|~r1_xboole_0(k2_xboole_0(X1,X2),X2)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_73, c_0_50])).
% 0.20/0.47  cnf(c_0_79, plain, (r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.47  cnf(c_0_80, negated_conjecture, (X1=k3_xboole_0(esk4_0,esk3_0)|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_31]), c_0_48])])).
% 0.20/0.47  cnf(c_0_81, negated_conjecture, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_48])])).
% 0.20/0.47  cnf(c_0_82, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_30]), c_0_30])])).
% 0.20/0.47  cnf(c_0_83, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_26, c_0_79])).
% 0.20/0.47  cnf(c_0_84, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_55])])).
% 0.20/0.47  cnf(c_0_85, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_82]), c_0_30])])).
% 0.20/0.47  cnf(c_0_86, negated_conjecture, (~r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.47  cnf(c_0_87, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85]), c_0_86]), ['proof']).
% 0.20/0.47  # SZS output end CNFRefutation
% 0.20/0.47  # Proof object total steps             : 88
% 0.20/0.47  # Proof object clause steps            : 55
% 0.20/0.47  # Proof object formula steps           : 33
% 0.20/0.47  # Proof object conjectures             : 16
% 0.20/0.47  # Proof object clause conjectures      : 13
% 0.20/0.47  # Proof object formula conjectures     : 3
% 0.20/0.47  # Proof object initial clauses used    : 20
% 0.20/0.47  # Proof object initial formulas used   : 16
% 0.20/0.47  # Proof object generating inferences   : 35
% 0.20/0.47  # Proof object simplifying inferences  : 25
% 0.20/0.47  # Training examples: 0 positive, 0 negative
% 0.20/0.47  # Parsed axioms                        : 22
% 0.20/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.47  # Initial clauses                      : 33
% 0.20/0.47  # Removed in clause preprocessing      : 0
% 0.20/0.47  # Initial clauses in saturation        : 33
% 0.20/0.47  # Processed clauses                    : 1492
% 0.20/0.47  # ...of these trivial                  : 41
% 0.20/0.47  # ...subsumed                          : 1010
% 0.20/0.47  # ...remaining for further processing  : 441
% 0.20/0.47  # Other redundant clauses eliminated   : 22
% 0.20/0.47  # Clauses deleted for lack of memory   : 0
% 0.20/0.47  # Backward-subsumed                    : 19
% 0.20/0.47  # Backward-rewritten                   : 42
% 0.20/0.47  # Generated clauses                    : 8839
% 0.20/0.47  # ...of the previous two non-trivial   : 6841
% 0.20/0.47  # Contextual simplify-reflections      : 5
% 0.20/0.47  # Paramodulations                      : 8817
% 0.20/0.47  # Factorizations                       : 0
% 0.20/0.47  # Equation resolutions                 : 22
% 0.20/0.47  # Propositional unsat checks           : 0
% 0.20/0.47  #    Propositional check models        : 0
% 0.20/0.47  #    Propositional check unsatisfiable : 0
% 0.20/0.47  #    Propositional clauses             : 0
% 0.20/0.47  #    Propositional clauses after purity: 0
% 0.20/0.47  #    Propositional unsat core size     : 0
% 0.20/0.47  #    Propositional preprocessing time  : 0.000
% 0.20/0.47  #    Propositional encoding time       : 0.000
% 0.20/0.47  #    Propositional solver time         : 0.000
% 0.20/0.47  #    Success case prop preproc time    : 0.000
% 0.20/0.47  #    Success case prop encoding time   : 0.000
% 0.20/0.47  #    Success case prop solver time     : 0.000
% 0.20/0.47  # Current number of processed clauses  : 347
% 0.20/0.47  #    Positive orientable unit clauses  : 53
% 0.20/0.47  #    Positive unorientable unit clauses: 0
% 0.20/0.47  #    Negative unit clauses             : 2
% 0.20/0.47  #    Non-unit-clauses                  : 292
% 0.20/0.47  # Current number of unprocessed clauses: 5235
% 0.20/0.47  # ...number of literals in the above   : 10969
% 0.20/0.47  # Current number of archived formulas  : 0
% 0.20/0.47  # Current number of archived clauses   : 93
% 0.20/0.47  # Clause-clause subsumption calls (NU) : 27102
% 0.20/0.47  # Rec. Clause-clause subsumption calls : 24608
% 0.20/0.47  # Non-unit clause-clause subsumptions  : 1021
% 0.20/0.47  # Unit Clause-clause subsumption calls : 297
% 0.20/0.47  # Rewrite failures with RHS unbound    : 0
% 0.20/0.47  # BW rewrite match attempts            : 115
% 0.20/0.47  # BW rewrite match successes           : 16
% 0.20/0.47  # Condensation attempts                : 0
% 0.20/0.47  # Condensation successes               : 0
% 0.20/0.47  # Termbank termtop insertions          : 79028
% 0.20/0.48  
% 0.20/0.48  # -------------------------------------------------
% 0.20/0.48  # User time                : 0.133 s
% 0.20/0.48  # System time              : 0.007 s
% 0.20/0.48  # Total time               : 0.140 s
% 0.20/0.48  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
