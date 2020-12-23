%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:27 EST 2020

% Result     : Theorem 1.21s
% Output     : CNFRefutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 172 expanded)
%              Number of clauses        :   41 (  78 expanded)
%              Number of leaves         :   14 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  158 ( 346 expanded)
%              Number of equality atoms :   25 (  96 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t73_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(t31_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(c_0_14,plain,(
    ! [X42,X43] : k3_tarski(k2_tarski(X42,X43)) = k2_xboole_0(X42,X43) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X40,X41] : k1_enumset1(X40,X40,X41) = k2_tarski(X40,X41) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X32,X33,X34] :
      ( ~ r1_tarski(X32,k2_xboole_0(X33,X34))
      | ~ r1_xboole_0(X32,X34)
      | r1_tarski(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).

cnf(c_0_17,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,X18)
      | r1_tarski(X17,k2_xboole_0(X19,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_20,plain,(
    ! [X65] :
      ( ~ v1_relat_1(X65)
      | k3_relat_1(X65) = k2_xboole_0(k1_relat_1(X65),k2_relat_1(X65)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_21,plain,(
    ! [X29,X30,X31] :
      ( ~ r1_tarski(k4_xboole_0(X29,X30),X31)
      | r1_tarski(X29,k2_xboole_0(X30,X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_24,plain,(
    ! [X24,X25] : r1_tarski(k4_xboole_0(X24,X25),X24) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_25,plain,(
    ! [X26,X27,X28] : k4_xboole_0(k4_xboole_0(X26,X27),X28) = k4_xboole_0(X26,k2_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_26,plain,(
    ! [X6] : k2_xboole_0(X6,X6) = X6 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_27,plain,(
    ! [X37,X38,X39] :
      ( ~ r1_tarski(X37,X38)
      | ~ r1_tarski(X39,X38)
      | r1_tarski(k2_xboole_0(X37,X39),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_30,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,X21)
      | ~ r1_tarski(X21,X22)
      | r1_tarski(X20,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_34,plain,(
    ! [X35,X36] :
      ( ( ~ r1_xboole_0(X35,X36)
        | k4_xboole_0(X35,X36) = X35 )
      & ( k4_xboole_0(X35,X36) != X35
        | r1_xboole_0(X35,X36) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X3,X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_23])).

cnf(c_0_39,plain,
    ( k3_relat_1(X1) = k3_tarski(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_29,c_0_23])).

fof(c_0_40,plain,(
    ! [X68,X69] :
      ( ( r1_tarski(k1_relat_1(X68),k1_relat_1(X69))
        | ~ r1_tarski(X68,X69)
        | ~ v1_relat_1(X69)
        | ~ v1_relat_1(X68) )
      & ( r1_tarski(k2_relat_1(X68),k2_relat_1(X69))
        | ~ r1_tarski(X68,X69)
        | ~ v1_relat_1(X69)
        | ~ v1_relat_1(X68) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_31,c_0_23])).

cnf(c_0_43,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(k1_enumset1(X1,X1,X2)),X3),X1)
    | ~ r1_xboole_0(k4_xboole_0(k3_tarski(k1_enumset1(X1,X1,X2)),X3),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_44,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k3_tarski(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_23])).

cnf(c_0_46,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_36,c_0_23])).

fof(c_0_47,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_relat_1])).

cnf(c_0_48,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_23])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_50,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ r1_tarski(k4_xboole_0(X4,X2),X3)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(k1_enumset1(X1,X1,X2)),X3),X1)
    | k4_xboole_0(k4_xboole_0(k3_tarski(k1_enumset1(X1,X1,X2)),X3),X2) != k4_xboole_0(k3_tarski(k1_enumset1(X1,X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_54,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & v1_relat_1(esk9_0)
    & r1_tarski(esk8_0,esk9_0)
    & ~ r1_tarski(k3_relat_1(esk8_0),k3_relat_1(esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_47])])])).

cnf(c_0_55,plain,
    ( r1_tarski(k3_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_39])).

cnf(c_0_56,plain,
    ( r1_tarski(k2_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k4_xboole_0(X3,k1_relat_1(X2)),k2_relat_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_51,c_0_39])).

cnf(c_0_58,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(k1_enumset1(X1,X1,X2)),X2),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk8_0),k3_relat_1(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,plain,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_relat_1(X1),k3_relat_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k3_tarski(k1_enumset1(k2_relat_1(X2),k2_relat_1(X2),k1_relat_1(X2)))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk8_0),k3_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62]),c_0_63])])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_38])).

cnf(c_0_67,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk8_0),k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_62])])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_62]),c_0_61]),c_0_63])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:14:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.21/1.42  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 1.21/1.42  # and selection function PSelectComplexExceptUniqMaxHorn.
% 1.21/1.42  #
% 1.21/1.42  # Preprocessing time       : 0.029 s
% 1.21/1.42  
% 1.21/1.42  # Proof found!
% 1.21/1.42  # SZS status Theorem
% 1.21/1.42  # SZS output start CNFRefutation
% 1.21/1.42  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.21/1.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.21/1.42  fof(t73_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 1.21/1.42  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.21/1.42  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 1.21/1.42  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 1.21/1.42  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.21/1.42  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.21/1.42  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.21/1.42  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.21/1.42  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.21/1.42  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.21/1.42  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 1.21/1.42  fof(t31_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 1.21/1.42  fof(c_0_14, plain, ![X42, X43]:k3_tarski(k2_tarski(X42,X43))=k2_xboole_0(X42,X43), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 1.21/1.42  fof(c_0_15, plain, ![X40, X41]:k1_enumset1(X40,X40,X41)=k2_tarski(X40,X41), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.21/1.42  fof(c_0_16, plain, ![X32, X33, X34]:(~r1_tarski(X32,k2_xboole_0(X33,X34))|~r1_xboole_0(X32,X34)|r1_tarski(X32,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).
% 1.21/1.42  cnf(c_0_17, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.21/1.42  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.21/1.42  fof(c_0_19, plain, ![X17, X18, X19]:(~r1_tarski(X17,X18)|r1_tarski(X17,k2_xboole_0(X19,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 1.21/1.42  fof(c_0_20, plain, ![X65]:(~v1_relat_1(X65)|k3_relat_1(X65)=k2_xboole_0(k1_relat_1(X65),k2_relat_1(X65))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 1.21/1.42  fof(c_0_21, plain, ![X29, X30, X31]:(~r1_tarski(k4_xboole_0(X29,X30),X31)|r1_tarski(X29,k2_xboole_0(X30,X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 1.21/1.42  cnf(c_0_22, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.21/1.42  cnf(c_0_23, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 1.21/1.42  fof(c_0_24, plain, ![X24, X25]:r1_tarski(k4_xboole_0(X24,X25),X24), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 1.21/1.42  fof(c_0_25, plain, ![X26, X27, X28]:k4_xboole_0(k4_xboole_0(X26,X27),X28)=k4_xboole_0(X26,k2_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 1.21/1.42  fof(c_0_26, plain, ![X6]:k2_xboole_0(X6,X6)=X6, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 1.21/1.42  fof(c_0_27, plain, ![X37, X38, X39]:(~r1_tarski(X37,X38)|~r1_tarski(X39,X38)|r1_tarski(k2_xboole_0(X37,X39),X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 1.21/1.42  cnf(c_0_28, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.21/1.42  cnf(c_0_29, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.21/1.42  fof(c_0_30, plain, ![X20, X21, X22]:(~r1_tarski(X20,X21)|~r1_tarski(X21,X22)|r1_tarski(X20,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 1.21/1.42  cnf(c_0_31, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.21/1.42  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)|~r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 1.21/1.42  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.21/1.42  fof(c_0_34, plain, ![X35, X36]:((~r1_xboole_0(X35,X36)|k4_xboole_0(X35,X36)=X35)&(k4_xboole_0(X35,X36)!=X35|r1_xboole_0(X35,X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 1.21/1.42  cnf(c_0_35, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.21/1.42  cnf(c_0_36, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.21/1.42  cnf(c_0_37, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.21/1.42  cnf(c_0_38, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X3,X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_23])).
% 1.21/1.42  cnf(c_0_39, plain, (k3_relat_1(X1)=k3_tarski(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_29, c_0_23])).
% 1.21/1.42  fof(c_0_40, plain, ![X68, X69]:((r1_tarski(k1_relat_1(X68),k1_relat_1(X69))|~r1_tarski(X68,X69)|~v1_relat_1(X69)|~v1_relat_1(X68))&(r1_tarski(k2_relat_1(X68),k2_relat_1(X69))|~r1_tarski(X68,X69)|~v1_relat_1(X69)|~v1_relat_1(X68))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 1.21/1.42  cnf(c_0_41, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.21/1.42  cnf(c_0_42, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_31, c_0_23])).
% 1.21/1.42  cnf(c_0_43, plain, (r1_tarski(k4_xboole_0(k3_tarski(k1_enumset1(X1,X1,X2)),X3),X1)|~r1_xboole_0(k4_xboole_0(k3_tarski(k1_enumset1(X1,X1,X2)),X3),X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 1.21/1.42  cnf(c_0_44, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.21/1.42  cnf(c_0_45, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k3_tarski(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_35, c_0_23])).
% 1.21/1.42  cnf(c_0_46, plain, (k3_tarski(k1_enumset1(X1,X1,X1))=X1), inference(rw,[status(thm)],[c_0_36, c_0_23])).
% 1.21/1.42  fof(c_0_47, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t31_relat_1])).
% 1.21/1.42  cnf(c_0_48, plain, (r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_37, c_0_23])).
% 1.21/1.42  cnf(c_0_49, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 1.21/1.42  cnf(c_0_50, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.21/1.42  cnf(c_0_51, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))|~r1_tarski(k4_xboole_0(X4,X2),X3)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.21/1.42  cnf(c_0_52, plain, (r1_tarski(k4_xboole_0(k3_tarski(k1_enumset1(X1,X1,X2)),X3),X1)|k4_xboole_0(k4_xboole_0(k3_tarski(k1_enumset1(X1,X1,X2)),X3),X2)!=k4_xboole_0(k3_tarski(k1_enumset1(X1,X1,X2)),X3)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 1.21/1.42  cnf(c_0_53, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 1.21/1.42  fof(c_0_54, negated_conjecture, (v1_relat_1(esk8_0)&(v1_relat_1(esk9_0)&(r1_tarski(esk8_0,esk9_0)&~r1_tarski(k3_relat_1(esk8_0),k3_relat_1(esk9_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_47])])])).
% 1.21/1.42  cnf(c_0_55, plain, (r1_tarski(k3_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_48, c_0_39])).
% 1.21/1.42  cnf(c_0_56, plain, (r1_tarski(k2_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 1.21/1.42  cnf(c_0_57, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(k4_xboole_0(X3,k1_relat_1(X2)),k2_relat_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_51, c_0_39])).
% 1.21/1.42  cnf(c_0_58, plain, (r1_tarski(k4_xboole_0(k3_tarski(k1_enumset1(X1,X1,X2)),X2),X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 1.21/1.42  cnf(c_0_59, negated_conjecture, (~r1_tarski(k3_relat_1(esk8_0),k3_relat_1(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.21/1.42  cnf(c_0_60, plain, (r1_tarski(k3_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k1_relat_1(X1),k3_relat_1(X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 1.21/1.42  cnf(c_0_61, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.21/1.42  cnf(c_0_62, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.21/1.42  cnf(c_0_63, negated_conjecture, (r1_tarski(esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.21/1.42  cnf(c_0_64, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k3_tarski(k1_enumset1(k2_relat_1(X2),k2_relat_1(X2),k1_relat_1(X2))))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 1.21/1.42  cnf(c_0_65, negated_conjecture, (~r1_tarski(k1_relat_1(esk8_0),k3_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_62]), c_0_63])])).
% 1.21/1.42  cnf(c_0_66, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_64, c_0_38])).
% 1.21/1.42  cnf(c_0_67, negated_conjecture, (~r1_tarski(k1_relat_1(esk8_0),k1_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_62])])).
% 1.21/1.42  cnf(c_0_68, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.21/1.42  cnf(c_0_69, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_62]), c_0_61]), c_0_63])]), ['proof']).
% 1.21/1.42  # SZS output end CNFRefutation
% 1.21/1.42  # Proof object total steps             : 70
% 1.21/1.42  # Proof object clause steps            : 41
% 1.21/1.42  # Proof object formula steps           : 29
% 1.21/1.42  # Proof object conjectures             : 10
% 1.21/1.42  # Proof object clause conjectures      : 7
% 1.21/1.42  # Proof object formula conjectures     : 3
% 1.21/1.42  # Proof object initial clauses used    : 18
% 1.21/1.42  # Proof object initial formulas used   : 14
% 1.21/1.42  # Proof object generating inferences   : 15
% 1.21/1.42  # Proof object simplifying inferences  : 18
% 1.21/1.42  # Training examples: 0 positive, 0 negative
% 1.21/1.42  # Parsed axioms                        : 22
% 1.21/1.42  # Removed by relevancy pruning/SinE    : 0
% 1.21/1.42  # Initial clauses                      : 38
% 1.21/1.42  # Removed in clause preprocessing      : 3
% 1.21/1.42  # Initial clauses in saturation        : 35
% 1.21/1.42  # Processed clauses                    : 5839
% 1.21/1.42  # ...of these trivial                  : 188
% 1.21/1.42  # ...subsumed                          : 4149
% 1.21/1.42  # ...remaining for further processing  : 1502
% 1.21/1.42  # Other redundant clauses eliminated   : 2
% 1.21/1.42  # Clauses deleted for lack of memory   : 0
% 1.21/1.42  # Backward-subsumed                    : 79
% 1.21/1.42  # Backward-rewritten                   : 7
% 1.21/1.42  # Generated clauses                    : 70895
% 1.21/1.42  # ...of the previous two non-trivial   : 66322
% 1.21/1.42  # Contextual simplify-reflections      : 54
% 1.21/1.42  # Paramodulations                      : 70869
% 1.21/1.42  # Factorizations                       : 6
% 1.21/1.42  # Equation resolutions                 : 20
% 1.21/1.42  # Propositional unsat checks           : 0
% 1.21/1.42  #    Propositional check models        : 0
% 1.21/1.42  #    Propositional check unsatisfiable : 0
% 1.21/1.42  #    Propositional clauses             : 0
% 1.21/1.42  #    Propositional clauses after purity: 0
% 1.21/1.42  #    Propositional unsat core size     : 0
% 1.21/1.42  #    Propositional preprocessing time  : 0.000
% 1.21/1.42  #    Propositional encoding time       : 0.000
% 1.21/1.42  #    Propositional solver time         : 0.000
% 1.21/1.42  #    Success case prop preproc time    : 0.000
% 1.21/1.42  #    Success case prop encoding time   : 0.000
% 1.21/1.42  #    Success case prop solver time     : 0.000
% 1.21/1.42  # Current number of processed clauses  : 1414
% 1.21/1.42  #    Positive orientable unit clauses  : 51
% 1.21/1.42  #    Positive unorientable unit clauses: 0
% 1.21/1.42  #    Negative unit clauses             : 18
% 1.21/1.42  #    Non-unit-clauses                  : 1345
% 1.21/1.42  # Current number of unprocessed clauses: 60414
% 1.21/1.42  # ...number of literals in the above   : 271204
% 1.21/1.42  # Current number of archived formulas  : 0
% 1.21/1.42  # Current number of archived clauses   : 89
% 1.21/1.42  # Clause-clause subsumption calls (NU) : 404709
% 1.21/1.42  # Rec. Clause-clause subsumption calls : 165160
% 1.21/1.42  # Non-unit clause-clause subsumptions  : 2756
% 1.21/1.42  # Unit Clause-clause subsumption calls : 8007
% 1.21/1.42  # Rewrite failures with RHS unbound    : 0
% 1.21/1.42  # BW rewrite match attempts            : 423
% 1.21/1.42  # BW rewrite match successes           : 5
% 1.21/1.42  # Condensation attempts                : 0
% 1.21/1.42  # Condensation successes               : 0
% 1.21/1.42  # Termbank termtop insertions          : 1161161
% 1.21/1.42  
% 1.21/1.42  # -------------------------------------------------
% 1.21/1.42  # User time                : 1.046 s
% 1.21/1.42  # System time              : 0.033 s
% 1.21/1.42  # Total time               : 1.079 s
% 1.21/1.42  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
