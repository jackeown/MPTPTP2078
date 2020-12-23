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
% DateTime   : Thu Dec  3 10:47:13 EST 2020

% Result     : Theorem 0.61s
% Output     : CNFRefutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 418 expanded)
%              Number of clauses        :   49 ( 187 expanded)
%              Number of leaves         :   14 ( 112 expanded)
%              Depth                    :   16
%              Number of atoms          :  268 (1345 expanded)
%              Number of equality atoms :  125 ( 849 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t7_tarski,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ! [X4] :
                  ~ ( r2_hidden(X4,X2)
                    & r2_hidden(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(t11_setfam_1,conjecture,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(c_0_14,plain,(
    ! [X21,X22,X23,X24,X25,X26,X27,X28,X29,X30] :
      ( ( ~ r2_hidden(X25,X24)
        | X25 = X21
        | X25 = X22
        | X25 = X23
        | X24 != k1_enumset1(X21,X22,X23) )
      & ( X26 != X21
        | r2_hidden(X26,X24)
        | X24 != k1_enumset1(X21,X22,X23) )
      & ( X26 != X22
        | r2_hidden(X26,X24)
        | X24 != k1_enumset1(X21,X22,X23) )
      & ( X26 != X23
        | r2_hidden(X26,X24)
        | X24 != k1_enumset1(X21,X22,X23) )
      & ( esk3_4(X27,X28,X29,X30) != X27
        | ~ r2_hidden(esk3_4(X27,X28,X29,X30),X30)
        | X30 = k1_enumset1(X27,X28,X29) )
      & ( esk3_4(X27,X28,X29,X30) != X28
        | ~ r2_hidden(esk3_4(X27,X28,X29,X30),X30)
        | X30 = k1_enumset1(X27,X28,X29) )
      & ( esk3_4(X27,X28,X29,X30) != X29
        | ~ r2_hidden(esk3_4(X27,X28,X29,X30),X30)
        | X30 = k1_enumset1(X27,X28,X29) )
      & ( r2_hidden(esk3_4(X27,X28,X29,X30),X30)
        | esk3_4(X27,X28,X29,X30) = X27
        | esk3_4(X27,X28,X29,X30) = X28
        | esk3_4(X27,X28,X29,X30) = X29
        | X30 = k1_enumset1(X27,X28,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_15,plain,(
    ! [X42,X43,X44] : k2_enumset1(X42,X42,X43,X44) = k1_enumset1(X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X45,X46,X47,X48] : k3_enumset1(X45,X45,X46,X47,X48) = k2_enumset1(X45,X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_17,plain,(
    ! [X32,X33,X34,X35,X36,X37] :
      ( ( ~ r2_hidden(X34,X33)
        | X34 = X32
        | X33 != k1_tarski(X32) )
      & ( X35 != X32
        | r2_hidden(X35,X33)
        | X33 != k1_tarski(X32) )
      & ( ~ r2_hidden(esk4_2(X36,X37),X37)
        | esk4_2(X36,X37) != X36
        | X37 = k1_tarski(X36) )
      & ( r2_hidden(esk4_2(X36,X37),X37)
        | esk4_2(X36,X37) = X36
        | X37 = k1_tarski(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_18,plain,(
    ! [X39] : k2_tarski(X39,X39) = k1_tarski(X39) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_19,plain,(
    ! [X40,X41] : k1_enumset1(X40,X40,X41) = k2_tarski(X40,X41) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X52,X53,X55] :
      ( ( r2_hidden(esk5_2(X52,X53),X53)
        | ~ r2_hidden(X52,X53) )
      & ( ~ r2_hidden(X55,X53)
        | ~ r2_hidden(X55,esk5_2(X52,X53))
        | ~ r2_hidden(X52,X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t11_setfam_1])).

cnf(c_0_29,plain,
    ( X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_21]),c_0_22])).

cnf(c_0_30,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_27])])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_33,negated_conjecture,(
    k1_setfam_1(k1_tarski(esk9_0)) != esk9_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

fof(c_0_34,plain,(
    ! [X57,X58,X59,X60,X61,X63,X66,X67,X68,X69] :
      ( ( ~ r2_hidden(X59,X58)
        | ~ r2_hidden(X60,X57)
        | r2_hidden(X59,X60)
        | X58 != k1_setfam_1(X57)
        | X57 = k1_xboole_0 )
      & ( r2_hidden(esk6_3(X57,X58,X61),X57)
        | r2_hidden(X61,X58)
        | X58 != k1_setfam_1(X57)
        | X57 = k1_xboole_0 )
      & ( ~ r2_hidden(X61,esk6_3(X57,X58,X61))
        | r2_hidden(X61,X58)
        | X58 != k1_setfam_1(X57)
        | X57 = k1_xboole_0 )
      & ( r2_hidden(esk8_2(X57,X63),X57)
        | ~ r2_hidden(esk7_2(X57,X63),X63)
        | X63 = k1_setfam_1(X57)
        | X57 = k1_xboole_0 )
      & ( ~ r2_hidden(esk7_2(X57,X63),esk8_2(X57,X63))
        | ~ r2_hidden(esk7_2(X57,X63),X63)
        | X63 = k1_setfam_1(X57)
        | X57 = k1_xboole_0 )
      & ( r2_hidden(esk7_2(X57,X63),X63)
        | ~ r2_hidden(X66,X57)
        | r2_hidden(esk7_2(X57,X63),X66)
        | X63 = k1_setfam_1(X57)
        | X57 = k1_xboole_0 )
      & ( X68 != k1_setfam_1(X67)
        | X68 = k1_xboole_0
        | X67 != k1_xboole_0 )
      & ( X69 != k1_xboole_0
        | X69 = k1_setfam_1(X67)
        | X67 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

fof(c_0_35,plain,(
    ! [X70,X71] :
      ( ( ~ m1_subset_1(X70,k1_zfmisc_1(X71))
        | r1_tarski(X70,X71) )
      & ( ~ r1_tarski(X70,X71)
        | m1_subset_1(X70,k1_zfmisc_1(X71)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_36,plain,(
    ! [X56] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X56)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( r2_hidden(esk5_2(X1,k3_enumset1(X2,X2,X2,X3,X1)),k3_enumset1(X2,X2,X2,X3,X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_21]),c_0_22])).

cnf(c_0_40,negated_conjecture,
    ( k1_setfam_1(k1_tarski(esk9_0)) != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( r2_hidden(esk7_2(X1,X2),X2)
    | r2_hidden(esk7_2(X1,X2),X3)
    | X2 = k1_setfam_1(X1)
    | X1 = k1_xboole_0
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_42,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk5_2(X3,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_46,plain,
    ( esk5_2(X1,k3_enumset1(X1,X1,X1,X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_39])])).

cnf(c_0_48,negated_conjecture,
    ( k1_setfam_1(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)) != esk9_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_24]),c_0_25]),c_0_21]),c_0_22])).

cnf(c_0_49,plain,
    ( X1 = k1_setfam_1(k3_enumset1(X2,X2,X2,X3,X4))
    | k3_enumset1(X2,X2,X2,X3,X4) = k1_xboole_0
    | r2_hidden(esk7_2(k3_enumset1(X2,X2,X2,X3,X4),X1),X1)
    | r2_hidden(esk7_2(k3_enumset1(X2,X2,X2,X3,X4),X1),X4) ),
    inference(spm,[status(thm)],[c_0_41,c_0_31])).

cnf(c_0_50,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_53,negated_conjecture,
    ( k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0) = k1_xboole_0
    | r2_hidden(esk7_2(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),esk9_0),esk9_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49])])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk7_2(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),esk9_0),esk9_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_56,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_57,plain,
    ( r2_hidden(esk8_2(X1,X2),X1)
    | X2 = k1_setfam_1(X1)
    | X1 = k1_xboole_0
    | ~ r2_hidden(esk7_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk7_2(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),esk9_0),esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_53]),c_0_55])).

fof(c_0_59,plain,(
    ! [X49,X50,X51] :
      ( ( r2_hidden(X49,X50)
        | ~ r2_hidden(X49,k4_xboole_0(X50,k1_tarski(X51))) )
      & ( X49 != X51
        | ~ r2_hidden(X49,k4_xboole_0(X50,k1_tarski(X51))) )
      & ( ~ r2_hidden(X49,X50)
        | X49 = X51
        | r2_hidden(X49,k4_xboole_0(X50,k1_tarski(X51))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

cnf(c_0_60,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_21]),c_0_22])).

cnf(c_0_61,negated_conjecture,
    ( k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0) = k1_xboole_0
    | r2_hidden(esk8_2(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),esk9_0),k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_48])).

cnf(c_0_62,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_63,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk8_2(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),esk9_0),k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))
    | r2_hidden(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_61])).

fof(c_0_65,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( r2_hidden(X15,X12)
        | ~ r2_hidden(X15,X14)
        | X14 != k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X16,X12)
        | r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X14 != k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk2_3(X17,X18,X19),X19)
        | ~ r2_hidden(esk2_3(X17,X18,X19),X17)
        | r2_hidden(esk2_3(X17,X18,X19),X18)
        | X19 = k4_xboole_0(X17,X18) )
      & ( r2_hidden(esk2_3(X17,X18,X19),X17)
        | r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k4_xboole_0(X17,X18) )
      & ( ~ r2_hidden(esk2_3(X17,X18,X19),X18)
        | r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k4_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_66,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k3_enumset1(X3,X3,X3,X3,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_24]),c_0_25]),c_0_21]),c_0_22])).

cnf(c_0_67,plain,
    ( X2 = k1_setfam_1(X1)
    | X1 = k1_xboole_0
    | ~ r2_hidden(esk7_2(X1,X2),esk8_2(X1,X2))
    | ~ r2_hidden(esk7_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_68,negated_conjecture,
    ( esk8_2(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),esk9_0) = esk9_0
    | r2_hidden(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_70,plain,
    ( X1 = X2
    | r2_hidden(X1,k4_xboole_0(k3_enumset1(X1,X1,X1,X3,X4),k3_enumset1(X2,X2,X2,X2,X2))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_47])).

cnf(c_0_71,negated_conjecture,
    ( k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0) = k1_xboole_0
    | r2_hidden(esk9_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_58])]),c_0_48])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk9_0,k4_xboole_0(k3_enumset1(esk9_0,esk9_0,esk9_0,X1,X2),k3_enumset1(k1_setfam_1(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)),k1_setfam_1(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)),k1_setfam_1(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)),k1_setfam_1(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)),k1_setfam_1(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_70])])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k3_enumset1(k1_setfam_1(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)),k1_setfam_1(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)),k1_setfam_1(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)),k1_setfam_1(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)),k1_setfam_1(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk9_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:04:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.61/0.78  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.61/0.78  # and selection function SelectNegativeLiterals.
% 0.61/0.78  #
% 0.61/0.78  # Preprocessing time       : 0.030 s
% 0.61/0.78  # Presaturation interreduction done
% 0.61/0.78  
% 0.61/0.78  # Proof found!
% 0.61/0.78  # SZS status Theorem
% 0.61/0.78  # SZS output start CNFRefutation
% 0.61/0.78  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.61/0.78  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.61/0.78  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.61/0.78  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.61/0.78  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.61/0.78  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.61/0.78  fof(t7_tarski, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X2)&r2_hidden(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 0.61/0.78  fof(t11_setfam_1, conjecture, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.61/0.78  fof(d1_setfam_1, axiom, ![X1, X2]:((X1!=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>![X4]:(r2_hidden(X4,X1)=>r2_hidden(X3,X4)))))&(X1=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>X2=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 0.61/0.78  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.61/0.78  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.61/0.78  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.61/0.78  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.61/0.78  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.61/0.78  fof(c_0_14, plain, ![X21, X22, X23, X24, X25, X26, X27, X28, X29, X30]:(((~r2_hidden(X25,X24)|(X25=X21|X25=X22|X25=X23)|X24!=k1_enumset1(X21,X22,X23))&(((X26!=X21|r2_hidden(X26,X24)|X24!=k1_enumset1(X21,X22,X23))&(X26!=X22|r2_hidden(X26,X24)|X24!=k1_enumset1(X21,X22,X23)))&(X26!=X23|r2_hidden(X26,X24)|X24!=k1_enumset1(X21,X22,X23))))&((((esk3_4(X27,X28,X29,X30)!=X27|~r2_hidden(esk3_4(X27,X28,X29,X30),X30)|X30=k1_enumset1(X27,X28,X29))&(esk3_4(X27,X28,X29,X30)!=X28|~r2_hidden(esk3_4(X27,X28,X29,X30),X30)|X30=k1_enumset1(X27,X28,X29)))&(esk3_4(X27,X28,X29,X30)!=X29|~r2_hidden(esk3_4(X27,X28,X29,X30),X30)|X30=k1_enumset1(X27,X28,X29)))&(r2_hidden(esk3_4(X27,X28,X29,X30),X30)|(esk3_4(X27,X28,X29,X30)=X27|esk3_4(X27,X28,X29,X30)=X28|esk3_4(X27,X28,X29,X30)=X29)|X30=k1_enumset1(X27,X28,X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.61/0.78  fof(c_0_15, plain, ![X42, X43, X44]:k2_enumset1(X42,X42,X43,X44)=k1_enumset1(X42,X43,X44), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.61/0.78  fof(c_0_16, plain, ![X45, X46, X47, X48]:k3_enumset1(X45,X45,X46,X47,X48)=k2_enumset1(X45,X46,X47,X48), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.61/0.78  fof(c_0_17, plain, ![X32, X33, X34, X35, X36, X37]:(((~r2_hidden(X34,X33)|X34=X32|X33!=k1_tarski(X32))&(X35!=X32|r2_hidden(X35,X33)|X33!=k1_tarski(X32)))&((~r2_hidden(esk4_2(X36,X37),X37)|esk4_2(X36,X37)!=X36|X37=k1_tarski(X36))&(r2_hidden(esk4_2(X36,X37),X37)|esk4_2(X36,X37)=X36|X37=k1_tarski(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.61/0.78  fof(c_0_18, plain, ![X39]:k2_tarski(X39,X39)=k1_tarski(X39), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.61/0.78  fof(c_0_19, plain, ![X40, X41]:k1_enumset1(X40,X40,X41)=k2_tarski(X40,X41), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.61/0.78  cnf(c_0_20, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.61/0.78  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.61/0.78  cnf(c_0_22, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.61/0.78  cnf(c_0_23, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.61/0.78  cnf(c_0_24, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.61/0.78  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.61/0.78  fof(c_0_26, plain, ![X52, X53, X55]:((r2_hidden(esk5_2(X52,X53),X53)|~r2_hidden(X52,X53))&(~r2_hidden(X55,X53)|~r2_hidden(X55,esk5_2(X52,X53))|~r2_hidden(X52,X53))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).
% 0.61/0.78  cnf(c_0_27, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.61/0.78  fof(c_0_28, negated_conjecture, ~(![X1]:k1_setfam_1(k1_tarski(X1))=X1), inference(assume_negation,[status(cth)],[t11_setfam_1])).
% 0.61/0.78  cnf(c_0_29, plain, (X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_21]), c_0_22])).
% 0.61/0.78  cnf(c_0_30, plain, (r2_hidden(esk5_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.61/0.78  cnf(c_0_31, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_27])])).
% 0.61/0.78  cnf(c_0_32, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.61/0.78  fof(c_0_33, negated_conjecture, k1_setfam_1(k1_tarski(esk9_0))!=esk9_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 0.61/0.78  fof(c_0_34, plain, ![X57, X58, X59, X60, X61, X63, X66, X67, X68, X69]:((((~r2_hidden(X59,X58)|(~r2_hidden(X60,X57)|r2_hidden(X59,X60))|X58!=k1_setfam_1(X57)|X57=k1_xboole_0)&((r2_hidden(esk6_3(X57,X58,X61),X57)|r2_hidden(X61,X58)|X58!=k1_setfam_1(X57)|X57=k1_xboole_0)&(~r2_hidden(X61,esk6_3(X57,X58,X61))|r2_hidden(X61,X58)|X58!=k1_setfam_1(X57)|X57=k1_xboole_0)))&(((r2_hidden(esk8_2(X57,X63),X57)|~r2_hidden(esk7_2(X57,X63),X63)|X63=k1_setfam_1(X57)|X57=k1_xboole_0)&(~r2_hidden(esk7_2(X57,X63),esk8_2(X57,X63))|~r2_hidden(esk7_2(X57,X63),X63)|X63=k1_setfam_1(X57)|X57=k1_xboole_0))&(r2_hidden(esk7_2(X57,X63),X63)|(~r2_hidden(X66,X57)|r2_hidden(esk7_2(X57,X63),X66))|X63=k1_setfam_1(X57)|X57=k1_xboole_0)))&((X68!=k1_setfam_1(X67)|X68=k1_xboole_0|X67!=k1_xboole_0)&(X69!=k1_xboole_0|X69=k1_setfam_1(X67)|X67!=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).
% 0.61/0.78  fof(c_0_35, plain, ![X70, X71]:((~m1_subset_1(X70,k1_zfmisc_1(X71))|r1_tarski(X70,X71))&(~r1_tarski(X70,X71)|m1_subset_1(X70,k1_zfmisc_1(X71)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.61/0.78  fof(c_0_36, plain, ![X56]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X56)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.61/0.78  cnf(c_0_37, plain, (X1=X2|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_29])).
% 0.61/0.78  cnf(c_0_38, plain, (r2_hidden(esk5_2(X1,k3_enumset1(X2,X2,X2,X3,X1)),k3_enumset1(X2,X2,X2,X3,X1))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.61/0.78  cnf(c_0_39, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_21]), c_0_22])).
% 0.61/0.78  cnf(c_0_40, negated_conjecture, (k1_setfam_1(k1_tarski(esk9_0))!=esk9_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.61/0.78  cnf(c_0_41, plain, (r2_hidden(esk7_2(X1,X2),X2)|r2_hidden(esk7_2(X1,X2),X3)|X2=k1_setfam_1(X1)|X1=k1_xboole_0|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.61/0.78  fof(c_0_42, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.61/0.78  cnf(c_0_43, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.61/0.78  cnf(c_0_44, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.61/0.78  cnf(c_0_45, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,esk5_2(X3,X2))|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.61/0.78  cnf(c_0_46, plain, (esk5_2(X1,k3_enumset1(X1,X1,X1,X1,X1))=X1), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.61/0.78  cnf(c_0_47, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_39])])).
% 0.61/0.78  cnf(c_0_48, negated_conjecture, (k1_setfam_1(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))!=esk9_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_24]), c_0_25]), c_0_21]), c_0_22])).
% 0.61/0.78  cnf(c_0_49, plain, (X1=k1_setfam_1(k3_enumset1(X2,X2,X2,X3,X4))|k3_enumset1(X2,X2,X2,X3,X4)=k1_xboole_0|r2_hidden(esk7_2(k3_enumset1(X2,X2,X2,X3,X4),X1),X1)|r2_hidden(esk7_2(k3_enumset1(X2,X2,X2,X3,X4),X1),X4)), inference(spm,[status(thm)],[c_0_41, c_0_31])).
% 0.61/0.78  cnf(c_0_50, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.61/0.78  cnf(c_0_51, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.61/0.78  cnf(c_0_52, plain, (~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))|~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.61/0.78  cnf(c_0_53, negated_conjecture, (k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)=k1_xboole_0|r2_hidden(esk7_2(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),esk9_0),esk9_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49])])).
% 0.61/0.78  cnf(c_0_54, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.61/0.78  cnf(c_0_55, negated_conjecture, (r2_hidden(esk7_2(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),esk9_0),esk9_0)|~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 0.61/0.78  cnf(c_0_56, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.61/0.78  cnf(c_0_57, plain, (r2_hidden(esk8_2(X1,X2),X1)|X2=k1_setfam_1(X1)|X1=k1_xboole_0|~r2_hidden(esk7_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.61/0.78  cnf(c_0_58, negated_conjecture, (r2_hidden(esk7_2(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),esk9_0),esk9_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_53]), c_0_55])).
% 0.61/0.78  fof(c_0_59, plain, ![X49, X50, X51]:(((r2_hidden(X49,X50)|~r2_hidden(X49,k4_xboole_0(X50,k1_tarski(X51))))&(X49!=X51|~r2_hidden(X49,k4_xboole_0(X50,k1_tarski(X51)))))&(~r2_hidden(X49,X50)|X49=X51|r2_hidden(X49,k4_xboole_0(X50,k1_tarski(X51))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.61/0.78  cnf(c_0_60, plain, (X1=X5|X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_21]), c_0_22])).
% 0.61/0.78  cnf(c_0_61, negated_conjecture, (k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)=k1_xboole_0|r2_hidden(esk8_2(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),esk9_0),k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_48])).
% 0.61/0.78  cnf(c_0_62, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.61/0.78  cnf(c_0_63, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_60])).
% 0.61/0.78  cnf(c_0_64, negated_conjecture, (r2_hidden(esk8_2(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),esk9_0),k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))|r2_hidden(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_61])).
% 0.61/0.78  fof(c_0_65, plain, ![X12, X13, X14, X15, X16, X17, X18, X19]:((((r2_hidden(X15,X12)|~r2_hidden(X15,X14)|X14!=k4_xboole_0(X12,X13))&(~r2_hidden(X15,X13)|~r2_hidden(X15,X14)|X14!=k4_xboole_0(X12,X13)))&(~r2_hidden(X16,X12)|r2_hidden(X16,X13)|r2_hidden(X16,X14)|X14!=k4_xboole_0(X12,X13)))&((~r2_hidden(esk2_3(X17,X18,X19),X19)|(~r2_hidden(esk2_3(X17,X18,X19),X17)|r2_hidden(esk2_3(X17,X18,X19),X18))|X19=k4_xboole_0(X17,X18))&((r2_hidden(esk2_3(X17,X18,X19),X17)|r2_hidden(esk2_3(X17,X18,X19),X19)|X19=k4_xboole_0(X17,X18))&(~r2_hidden(esk2_3(X17,X18,X19),X18)|r2_hidden(esk2_3(X17,X18,X19),X19)|X19=k4_xboole_0(X17,X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.61/0.78  cnf(c_0_66, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k3_enumset1(X3,X3,X3,X3,X3)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_24]), c_0_25]), c_0_21]), c_0_22])).
% 0.61/0.78  cnf(c_0_67, plain, (X2=k1_setfam_1(X1)|X1=k1_xboole_0|~r2_hidden(esk7_2(X1,X2),esk8_2(X1,X2))|~r2_hidden(esk7_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.61/0.78  cnf(c_0_68, negated_conjecture, (esk8_2(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0),esk9_0)=esk9_0|r2_hidden(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.61/0.78  cnf(c_0_69, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.61/0.78  cnf(c_0_70, plain, (X1=X2|r2_hidden(X1,k4_xboole_0(k3_enumset1(X1,X1,X1,X3,X4),k3_enumset1(X2,X2,X2,X2,X2)))), inference(spm,[status(thm)],[c_0_66, c_0_47])).
% 0.61/0.78  cnf(c_0_71, negated_conjecture, (k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)=k1_xboole_0|r2_hidden(esk9_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_58])]), c_0_48])).
% 0.61/0.78  cnf(c_0_72, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_69])).
% 0.61/0.78  cnf(c_0_73, negated_conjecture, (r2_hidden(esk9_0,k4_xboole_0(k3_enumset1(esk9_0,esk9_0,esk9_0,X1,X2),k3_enumset1(k1_setfam_1(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)),k1_setfam_1(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)),k1_setfam_1(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)),k1_setfam_1(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)),k1_setfam_1(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)))))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_70])])).
% 0.61/0.78  cnf(c_0_74, negated_conjecture, (r2_hidden(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_71])).
% 0.61/0.78  cnf(c_0_75, negated_conjecture, (~r2_hidden(esk9_0,k3_enumset1(k1_setfam_1(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)),k1_setfam_1(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)),k1_setfam_1(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)),k1_setfam_1(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)),k1_setfam_1(k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0))))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.61/0.78  cnf(c_0_76, negated_conjecture, (r2_hidden(esk9_0,X1)), inference(spm,[status(thm)],[c_0_54, c_0_74])).
% 0.61/0.78  cnf(c_0_77, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76])]), ['proof']).
% 0.61/0.78  # SZS output end CNFRefutation
% 0.61/0.78  # Proof object total steps             : 78
% 0.61/0.78  # Proof object clause steps            : 49
% 0.61/0.78  # Proof object formula steps           : 29
% 0.61/0.78  # Proof object conjectures             : 17
% 0.61/0.78  # Proof object clause conjectures      : 14
% 0.61/0.78  # Proof object formula conjectures     : 3
% 0.61/0.78  # Proof object initial clauses used    : 19
% 0.61/0.78  # Proof object initial formulas used   : 14
% 0.61/0.78  # Proof object generating inferences   : 18
% 0.61/0.78  # Proof object simplifying inferences  : 37
% 0.61/0.78  # Training examples: 0 positive, 0 negative
% 0.61/0.78  # Parsed axioms                        : 15
% 0.61/0.78  # Removed by relevancy pruning/SinE    : 0
% 0.61/0.78  # Initial clauses                      : 43
% 0.61/0.78  # Removed in clause preprocessing      : 4
% 0.61/0.78  # Initial clauses in saturation        : 39
% 0.61/0.78  # Processed clauses                    : 1152
% 0.61/0.78  # ...of these trivial                  : 22
% 0.61/0.78  # ...subsumed                          : 650
% 0.61/0.78  # ...remaining for further processing  : 480
% 0.61/0.78  # Other redundant clauses eliminated   : 1060
% 0.61/0.78  # Clauses deleted for lack of memory   : 0
% 0.61/0.78  # Backward-subsumed                    : 13
% 0.61/0.78  # Backward-rewritten                   : 60
% 0.61/0.78  # Generated clauses                    : 24095
% 0.61/0.78  # ...of the previous two non-trivial   : 22753
% 0.61/0.78  # Contextual simplify-reflections      : 5
% 0.61/0.78  # Paramodulations                      : 23029
% 0.61/0.78  # Factorizations                       : 12
% 0.61/0.78  # Equation resolutions                 : 1060
% 0.61/0.78  # Propositional unsat checks           : 0
% 0.61/0.78  #    Propositional check models        : 0
% 0.61/0.78  #    Propositional check unsatisfiable : 0
% 0.61/0.78  #    Propositional clauses             : 0
% 0.61/0.78  #    Propositional clauses after purity: 0
% 0.61/0.78  #    Propositional unsat core size     : 0
% 0.61/0.78  #    Propositional preprocessing time  : 0.000
% 0.61/0.78  #    Propositional encoding time       : 0.000
% 0.61/0.78  #    Propositional solver time         : 0.000
% 0.61/0.78  #    Success case prop preproc time    : 0.000
% 0.61/0.78  #    Success case prop encoding time   : 0.000
% 0.61/0.78  #    Success case prop solver time     : 0.000
% 0.61/0.78  # Current number of processed clauses  : 356
% 0.61/0.78  #    Positive orientable unit clauses  : 18
% 0.61/0.78  #    Positive unorientable unit clauses: 0
% 0.61/0.78  #    Negative unit clauses             : 4
% 0.61/0.78  #    Non-unit-clauses                  : 334
% 0.61/0.78  # Current number of unprocessed clauses: 21646
% 0.61/0.78  # ...number of literals in the above   : 95066
% 0.61/0.78  # Current number of archived formulas  : 0
% 0.61/0.78  # Current number of archived clauses   : 113
% 0.61/0.78  # Clause-clause subsumption calls (NU) : 29604
% 0.61/0.78  # Rec. Clause-clause subsumption calls : 15579
% 0.61/0.78  # Non-unit clause-clause subsumptions  : 583
% 0.61/0.78  # Unit Clause-clause subsumption calls : 915
% 0.61/0.78  # Rewrite failures with RHS unbound    : 0
% 0.61/0.78  # BW rewrite match attempts            : 63
% 0.61/0.78  # BW rewrite match successes           : 33
% 0.61/0.78  # Condensation attempts                : 0
% 0.61/0.78  # Condensation successes               : 0
% 0.61/0.78  # Termbank termtop insertions          : 659987
% 0.61/0.79  
% 0.61/0.79  # -------------------------------------------------
% 0.61/0.79  # User time                : 0.424 s
% 0.61/0.79  # System time              : 0.016 s
% 0.61/0.79  # Total time               : 0.440 s
% 0.61/0.79  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
