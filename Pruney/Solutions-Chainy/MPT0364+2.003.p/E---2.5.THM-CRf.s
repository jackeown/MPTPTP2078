%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:31 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  119 (1789 expanded)
%              Number of clauses        :   75 ( 811 expanded)
%              Number of leaves         :   22 ( 486 expanded)
%              Depth                    :   19
%              Number of atoms          :  232 (2032 expanded)
%              Number of equality atoms :   63 (1642 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t44_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,k3_subset_1(X1,X3))
          <=> r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(t81_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
     => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_22,plain,(
    ! [X27,X28] : k2_xboole_0(k3_xboole_0(X27,X28),k4_xboole_0(X27,X28)) = X27 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_23,plain,(
    ! [X20,X21] : k4_xboole_0(X20,X21) = k5_xboole_0(X20,k3_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_24,plain,(
    ! [X44,X45] : k3_xboole_0(X44,X45) = k5_xboole_0(k5_xboole_0(X44,X45),k2_xboole_0(X44,X45)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

fof(c_0_25,plain,(
    ! [X24] : k3_xboole_0(X24,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_26,plain,(
    ! [X25,X26] : r1_tarski(k4_xboole_0(X25,X26),X25) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_27,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X41,X42,X43] : k5_xboole_0(k5_xboole_0(X41,X42),X43) = k5_xboole_0(X41,k5_xboole_0(X42,X43)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_31,plain,(
    ! [X29] : k5_xboole_0(X29,k1_xboole_0) = X29 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_32,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k2_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_29])).

cnf(c_0_36,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_33,c_0_29])).

fof(c_0_40,plain,(
    ! [X22,X23] :
      ( ~ r1_tarski(X22,X23)
      | k2_xboole_0(X22,X23) = X23 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_41,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_28]),c_0_29])).

cnf(c_0_42,plain,
    ( k2_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))),k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_36])).

cnf(c_0_43,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_39,c_0_37])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))),X1) ),
    inference(rw,[status(thm)],[c_0_41,c_0_36])).

cnf(c_0_47,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_44]),c_0_37])).

fof(c_0_48,plain,(
    ! [X55,X56] :
      ( ~ m1_subset_1(X56,k1_zfmisc_1(X55))
      | k3_subset_1(X55,X56) = k4_xboole_0(X55,X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_37])).

cnf(c_0_50,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_43]),c_0_43])).

fof(c_0_51,plain,(
    ! [X36,X37,X38] :
      ( ~ r1_tarski(X36,X37)
      | r1_xboole_0(X36,k4_xboole_0(X38,X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

cnf(c_0_52,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,k1_xboole_0),X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_44]),c_0_43])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_56,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_xboole_0(X2,k3_subset_1(X1,X3))
            <=> r1_tarski(X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t44_subset_1])).

cnf(c_0_57,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_28]),c_0_29])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_37])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X3,X2),k2_xboole_0(X3,X2))))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_28]),c_0_29])).

fof(c_0_60,plain,(
    ! [X33,X34,X35] :
      ( ~ r1_xboole_0(X33,k4_xboole_0(X34,X35))
      | r1_xboole_0(X34,k4_xboole_0(X33,X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).

fof(c_0_61,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))
    & ( ~ r1_xboole_0(esk5_0,k3_subset_1(esk4_0,esk6_0))
      | ~ r1_tarski(esk5_0,esk6_0) )
    & ( r1_xboole_0(esk5_0,k3_subset_1(esk4_0,esk6_0))
      | r1_tarski(esk5_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_56])])])).

cnf(c_0_62,plain,
    ( k3_subset_1(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_57,c_0_36])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_53,c_0_58])).

cnf(c_0_64,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3)))))
    | ~ r1_tarski(X1,X3) ),
    inference(rw,[status(thm)],[c_0_59,c_0_36])).

fof(c_0_65,plain,(
    ! [X46,X47,X48,X49,X50,X51] :
      ( ( ~ r2_hidden(X48,X47)
        | r1_tarski(X48,X46)
        | X47 != k1_zfmisc_1(X46) )
      & ( ~ r1_tarski(X49,X46)
        | r2_hidden(X49,X47)
        | X47 != k1_zfmisc_1(X46) )
      & ( ~ r2_hidden(esk3_2(X50,X51),X51)
        | ~ r1_tarski(esk3_2(X50,X51),X50)
        | X51 = k1_zfmisc_1(X50) )
      & ( r2_hidden(esk3_2(X50,X51),X51)
        | r1_tarski(esk3_2(X50,X51),X50)
        | X51 = k1_zfmisc_1(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_66,plain,(
    ! [X53,X54] :
      ( ( ~ m1_subset_1(X54,X53)
        | r2_hidden(X54,X53)
        | v1_xboole_0(X53) )
      & ( ~ r2_hidden(X54,X53)
        | m1_subset_1(X54,X53)
        | v1_xboole_0(X53) )
      & ( ~ m1_subset_1(X54,X53)
        | v1_xboole_0(X54)
        | ~ v1_xboole_0(X53) )
      & ( ~ v1_xboole_0(X54)
        | m1_subset_1(X54,X53)
        | ~ v1_xboole_0(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_67,plain,(
    ! [X57] : ~ v1_xboole_0(k1_zfmisc_1(X57)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_68,plain,
    ( r1_xboole_0(X2,k4_xboole_0(X1,X3))
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_xboole_0(esk5_0,k3_subset_1(esk4_0,esk6_0))
    | ~ r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,plain,
    ( k3_subset_1(X1,X2) = k5_xboole_0(X2,k2_xboole_0(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_72,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_64,c_0_63])).

fof(c_0_73,plain,(
    ! [X12,X13,X15,X16,X17] :
      ( ( r1_xboole_0(X12,X13)
        | r2_hidden(esk2_2(X12,X13),k3_xboole_0(X12,X13)) )
      & ( ~ r2_hidden(X17,k3_xboole_0(X15,X16))
        | ~ r1_xboole_0(X15,X16) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_74,plain,(
    ! [X18,X19] :
      ( ( k4_xboole_0(X18,X19) != k1_xboole_0
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | k4_xboole_0(X18,X19) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_78,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_79,plain,
    ( r1_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X3),k2_xboole_0(X1,X3))))
    | ~ r1_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_28]),c_0_28]),c_0_29]),c_0_29])).

cnf(c_0_80,negated_conjecture,
    ( r1_xboole_0(esk5_0,k3_subset_1(esk4_0,esk6_0))
    | r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_tarski(esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])]),c_0_72])).

cnf(c_0_82,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_83,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

fof(c_0_84,plain,(
    ! [X30,X31,X32] :
      ( ~ r1_tarski(X30,X31)
      | ~ r1_xboole_0(X31,X32)
      | r1_xboole_0(X30,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_75])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

cnf(c_0_87,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3)))))
    | ~ r1_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X3,k2_xboole_0(X1,X3))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_36]),c_0_36])).

cnf(c_0_88,negated_conjecture,
    ( r1_xboole_0(esk5_0,k3_subset_1(esk4_0,esk6_0)) ),
    inference(sr,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_89,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_82,c_0_29])).

fof(c_0_90,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_91,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_28]),c_0_29])).

cnf(c_0_92,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_94,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X3,X2)))
    | ~ r1_xboole_0(X3,k5_xboole_0(X2,k2_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_63]),c_0_63])).

cnf(c_0_95,negated_conjecture,
    ( r1_xboole_0(esk5_0,k5_xboole_0(esk6_0,k2_xboole_0(esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_70]),c_0_71])])).

cnf(c_0_96,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))) ),
    inference(rw,[status(thm)],[c_0_89,c_0_36])).

cnf(c_0_97,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_98,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_91,c_0_36])).

cnf(c_0_99,negated_conjecture,
    ( r1_xboole_0(esk5_0,X1)
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_100,negated_conjecture,
    ( r1_xboole_0(esk4_0,k5_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_101,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

fof(c_0_102,plain,(
    ! [X39,X40] :
      ( ~ v1_xboole_0(X39)
      | X39 = X40
      | ~ v1_xboole_0(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_103,plain,
    ( v1_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_104,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[c_0_98,c_0_63])).

cnf(c_0_105,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_43]),c_0_43]),c_0_44]),c_0_37]),c_0_44]),c_0_37])).

cnf(c_0_106,negated_conjecture,
    ( r1_xboole_0(esk5_0,k5_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_107,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_28]),c_0_29])).

cnf(c_0_108,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_109,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_110,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_37])).

cnf(c_0_111,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_112,plain,
    ( r1_tarski(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X2) ),
    inference(rw,[status(thm)],[c_0_46,c_0_63])).

cnf(c_0_113,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_107,c_0_36])).

cnf(c_0_114,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_115,negated_conjecture,
    ( v1_xboole_0(k5_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_112])])).

cnf(c_0_116,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X2,k2_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_113,c_0_63])).

cnf(c_0_117,negated_conjecture,
    ( k5_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_118,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_81]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:36:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.028 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.20/0.41  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.41  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.20/0.41  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.41  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.41  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.20/0.41  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.20/0.41  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.20/0.41  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.41  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.20/0.41  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.20/0.41  fof(t44_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_xboole_0(X2,k3_subset_1(X1,X3))<=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 0.20/0.41  fof(t81_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 0.20/0.41  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.41  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.41  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.20/0.41  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.41  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.20/0.41  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.20/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.41  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 0.20/0.41  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.41  fof(c_0_22, plain, ![X27, X28]:k2_xboole_0(k3_xboole_0(X27,X28),k4_xboole_0(X27,X28))=X27, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.20/0.41  fof(c_0_23, plain, ![X20, X21]:k4_xboole_0(X20,X21)=k5_xboole_0(X20,k3_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.41  fof(c_0_24, plain, ![X44, X45]:k3_xboole_0(X44,X45)=k5_xboole_0(k5_xboole_0(X44,X45),k2_xboole_0(X44,X45)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.20/0.41  fof(c_0_25, plain, ![X24]:k3_xboole_0(X24,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.41  fof(c_0_26, plain, ![X25, X26]:r1_tarski(k4_xboole_0(X25,X26),X25), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.41  cnf(c_0_27, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  cnf(c_0_29, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.41  fof(c_0_30, plain, ![X41, X42, X43]:k5_xboole_0(k5_xboole_0(X41,X42),X43)=k5_xboole_0(X41,k5_xboole_0(X42,X43)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.20/0.41  fof(c_0_31, plain, ![X29]:k5_xboole_0(X29,k1_xboole_0)=X29, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.20/0.41  fof(c_0_32, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k5_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.20/0.41  cnf(c_0_33, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  cnf(c_0_34, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  cnf(c_0_35, plain, (k2_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_29])).
% 0.20/0.41  cnf(c_0_36, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.41  cnf(c_0_37, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.41  cnf(c_0_38, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.41  cnf(c_0_39, plain, (k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_33, c_0_29])).
% 0.20/0.41  fof(c_0_40, plain, ![X22, X23]:(~r1_tarski(X22,X23)|k2_xboole_0(X22,X23)=X23), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.41  cnf(c_0_41, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_28]), c_0_29])).
% 0.20/0.41  cnf(c_0_42, plain, (k2_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))),k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_36])).
% 0.20/0.41  cnf(c_0_43, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.41  cnf(c_0_44, plain, (k5_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_39, c_0_37])).
% 0.20/0.41  cnf(c_0_45, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.41  cnf(c_0_46, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))),X1)), inference(rw,[status(thm)],[c_0_41, c_0_36])).
% 0.20/0.41  cnf(c_0_47, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_44]), c_0_37])).
% 0.20/0.41  fof(c_0_48, plain, ![X55, X56]:(~m1_subset_1(X56,k1_zfmisc_1(X55))|k3_subset_1(X55,X56)=k4_xboole_0(X55,X56)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.20/0.41  cnf(c_0_49, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_37])).
% 0.20/0.41  cnf(c_0_50, plain, (r1_tarski(k5_xboole_0(X1,X1),k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_43]), c_0_43])).
% 0.20/0.41  fof(c_0_51, plain, ![X36, X37, X38]:(~r1_tarski(X36,X37)|r1_xboole_0(X36,k4_xboole_0(X38,X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.20/0.41  cnf(c_0_52, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.41  cnf(c_0_53, plain, (k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,k1_xboole_0),X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_44]), c_0_43])).
% 0.20/0.41  cnf(c_0_54, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.41  cnf(c_0_55, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.41  fof(c_0_56, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_xboole_0(X2,k3_subset_1(X1,X3))<=>r1_tarski(X2,X3))))), inference(assume_negation,[status(cth)],[t44_subset_1])).
% 0.20/0.41  cnf(c_0_57, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_28]), c_0_29])).
% 0.20/0.41  cnf(c_0_58, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_37])).
% 0.20/0.41  cnf(c_0_59, plain, (r1_xboole_0(X1,k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X3,X2),k2_xboole_0(X3,X2))))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_28]), c_0_29])).
% 0.20/0.41  fof(c_0_60, plain, ![X33, X34, X35]:(~r1_xboole_0(X33,k4_xboole_0(X34,X35))|r1_xboole_0(X34,k4_xboole_0(X33,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).
% 0.20/0.41  fof(c_0_61, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))&((~r1_xboole_0(esk5_0,k3_subset_1(esk4_0,esk6_0))|~r1_tarski(esk5_0,esk6_0))&(r1_xboole_0(esk5_0,k3_subset_1(esk4_0,esk6_0))|r1_tarski(esk5_0,esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_56])])])).
% 0.20/0.41  cnf(c_0_62, plain, (k3_subset_1(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_57, c_0_36])).
% 0.20/0.41  cnf(c_0_63, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[c_0_53, c_0_58])).
% 0.20/0.41  cnf(c_0_64, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3)))))|~r1_tarski(X1,X3)), inference(rw,[status(thm)],[c_0_59, c_0_36])).
% 0.20/0.41  fof(c_0_65, plain, ![X46, X47, X48, X49, X50, X51]:(((~r2_hidden(X48,X47)|r1_tarski(X48,X46)|X47!=k1_zfmisc_1(X46))&(~r1_tarski(X49,X46)|r2_hidden(X49,X47)|X47!=k1_zfmisc_1(X46)))&((~r2_hidden(esk3_2(X50,X51),X51)|~r1_tarski(esk3_2(X50,X51),X50)|X51=k1_zfmisc_1(X50))&(r2_hidden(esk3_2(X50,X51),X51)|r1_tarski(esk3_2(X50,X51),X50)|X51=k1_zfmisc_1(X50)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.41  fof(c_0_66, plain, ![X53, X54]:(((~m1_subset_1(X54,X53)|r2_hidden(X54,X53)|v1_xboole_0(X53))&(~r2_hidden(X54,X53)|m1_subset_1(X54,X53)|v1_xboole_0(X53)))&((~m1_subset_1(X54,X53)|v1_xboole_0(X54)|~v1_xboole_0(X53))&(~v1_xboole_0(X54)|m1_subset_1(X54,X53)|~v1_xboole_0(X53)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.41  fof(c_0_67, plain, ![X57]:~v1_xboole_0(k1_zfmisc_1(X57)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.20/0.41  cnf(c_0_68, plain, (r1_xboole_0(X2,k4_xboole_0(X1,X3))|~r1_xboole_0(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.41  cnf(c_0_69, negated_conjecture, (~r1_xboole_0(esk5_0,k3_subset_1(esk4_0,esk6_0))|~r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.41  cnf(c_0_70, plain, (k3_subset_1(X1,X2)=k5_xboole_0(X2,k2_xboole_0(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.41  cnf(c_0_71, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.41  cnf(c_0_72, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_64, c_0_63])).
% 0.20/0.41  fof(c_0_73, plain, ![X12, X13, X15, X16, X17]:((r1_xboole_0(X12,X13)|r2_hidden(esk2_2(X12,X13),k3_xboole_0(X12,X13)))&(~r2_hidden(X17,k3_xboole_0(X15,X16))|~r1_xboole_0(X15,X16))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.41  fof(c_0_74, plain, ![X18, X19]:((k4_xboole_0(X18,X19)!=k1_xboole_0|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|k4_xboole_0(X18,X19)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.20/0.41  cnf(c_0_75, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.41  cnf(c_0_76, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.41  cnf(c_0_77, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.41  cnf(c_0_78, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.41  cnf(c_0_79, plain, (r1_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X3),k2_xboole_0(X1,X3))))|~r1_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_28]), c_0_28]), c_0_29]), c_0_29])).
% 0.20/0.41  cnf(c_0_80, negated_conjecture, (r1_xboole_0(esk5_0,k3_subset_1(esk4_0,esk6_0))|r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.41  cnf(c_0_81, negated_conjecture, (~r1_tarski(esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])]), c_0_72])).
% 0.20/0.41  cnf(c_0_82, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.20/0.41  cnf(c_0_83, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.41  fof(c_0_84, plain, ![X30, X31, X32]:(~r1_tarski(X30,X31)|~r1_xboole_0(X31,X32)|r1_xboole_0(X30,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.20/0.41  cnf(c_0_85, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_75])).
% 0.20/0.41  cnf(c_0_86, negated_conjecture, (r2_hidden(esk5_0,k1_zfmisc_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])).
% 0.20/0.41  cnf(c_0_87, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3)))))|~r1_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X3,k2_xboole_0(X1,X3)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_36]), c_0_36])).
% 0.20/0.41  cnf(c_0_88, negated_conjecture, (r1_xboole_0(esk5_0,k3_subset_1(esk4_0,esk6_0))), inference(sr,[status(thm)],[c_0_80, c_0_81])).
% 0.20/0.41  cnf(c_0_89, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_82, c_0_29])).
% 0.20/0.41  fof(c_0_90, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.41  cnf(c_0_91, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_28]), c_0_29])).
% 0.20/0.41  cnf(c_0_92, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.20/0.41  cnf(c_0_93, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.20/0.41  cnf(c_0_94, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X3,X2)))|~r1_xboole_0(X3,k5_xboole_0(X2,k2_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_63]), c_0_63])).
% 0.20/0.41  cnf(c_0_95, negated_conjecture, (r1_xboole_0(esk5_0,k5_xboole_0(esk6_0,k2_xboole_0(esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_70]), c_0_71])])).
% 0.20/0.41  cnf(c_0_96, plain, (~r1_xboole_0(X1,X2)|~r2_hidden(X3,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))), inference(rw,[status(thm)],[c_0_89, c_0_36])).
% 0.20/0.41  cnf(c_0_97, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.20/0.41  cnf(c_0_98, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_91, c_0_36])).
% 0.20/0.41  cnf(c_0_99, negated_conjecture, (r1_xboole_0(esk5_0,X1)|~r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.20/0.41  cnf(c_0_100, negated_conjecture, (r1_xboole_0(esk4_0,k5_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk6_0)))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.20/0.41  cnf(c_0_101, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.41  fof(c_0_102, plain, ![X39, X40]:(~v1_xboole_0(X39)|X39=X40|~v1_xboole_0(X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.20/0.41  cnf(c_0_103, plain, (v1_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.20/0.41  cnf(c_0_104, plain, (k5_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[c_0_98, c_0_63])).
% 0.20/0.41  cnf(c_0_105, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_43]), c_0_43]), c_0_44]), c_0_37]), c_0_44]), c_0_37])).
% 0.20/0.41  cnf(c_0_106, negated_conjecture, (r1_xboole_0(esk5_0,k5_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk6_0)))), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.20/0.41  cnf(c_0_107, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_28]), c_0_29])).
% 0.20/0.41  cnf(c_0_108, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.20/0.41  cnf(c_0_109, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.41  cnf(c_0_110, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_37])).
% 0.20/0.41  cnf(c_0_111, negated_conjecture, (r1_xboole_0(k5_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 0.20/0.41  cnf(c_0_112, plain, (r1_tarski(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X2)), inference(rw,[status(thm)],[c_0_46, c_0_63])).
% 0.20/0.41  cnf(c_0_113, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_107, c_0_36])).
% 0.20/0.41  cnf(c_0_114, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 0.20/0.41  cnf(c_0_115, negated_conjecture, (v1_xboole_0(k5_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_112])])).
% 0.20/0.41  cnf(c_0_116, plain, (r1_tarski(X1,X2)|k5_xboole_0(X2,k2_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_113, c_0_63])).
% 0.20/0.41  cnf(c_0_117, negated_conjecture, (k5_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk6_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_114, c_0_115])).
% 0.20/0.41  cnf(c_0_118, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_81]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 119
% 0.20/0.41  # Proof object clause steps            : 75
% 0.20/0.41  # Proof object formula steps           : 44
% 0.20/0.41  # Proof object conjectures             : 19
% 0.20/0.41  # Proof object clause conjectures      : 16
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 26
% 0.20/0.41  # Proof object initial formulas used   : 22
% 0.20/0.41  # Proof object generating inferences   : 22
% 0.20/0.41  # Proof object simplifying inferences  : 63
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 23
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 35
% 0.20/0.41  # Removed in clause preprocessing      : 2
% 0.20/0.41  # Initial clauses in saturation        : 33
% 0.20/0.41  # Processed clauses                    : 430
% 0.20/0.41  # ...of these trivial                  : 24
% 0.20/0.41  # ...subsumed                          : 203
% 0.20/0.41  # ...remaining for further processing  : 203
% 0.20/0.41  # Other redundant clauses eliminated   : 5
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 0
% 0.20/0.41  # Backward-rewritten                   : 41
% 0.20/0.41  # Generated clauses                    : 1624
% 0.20/0.41  # ...of the previous two non-trivial   : 1382
% 0.20/0.41  # Contextual simplify-reflections      : 2
% 0.20/0.41  # Paramodulations                      : 1611
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 5
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 119
% 0.20/0.41  #    Positive orientable unit clauses  : 51
% 0.20/0.41  #    Positive unorientable unit clauses: 6
% 0.20/0.41  #    Negative unit clauses             : 6
% 0.20/0.41  #    Non-unit-clauses                  : 56
% 0.20/0.41  # Current number of unprocessed clauses: 965
% 0.20/0.41  # ...number of literals in the above   : 2206
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 84
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 1354
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 1081
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 72
% 0.20/0.41  # Unit Clause-clause subsumption calls : 148
% 0.20/0.41  # Rewrite failures with RHS unbound    : 6
% 0.20/0.41  # BW rewrite match attempts            : 172
% 0.20/0.41  # BW rewrite match successes           : 100
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 18622
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.060 s
% 0.20/0.41  # System time              : 0.002 s
% 0.20/0.41  # Total time               : 0.062 s
% 0.20/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
