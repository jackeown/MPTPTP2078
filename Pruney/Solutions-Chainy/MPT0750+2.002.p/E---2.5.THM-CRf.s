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
% DateTime   : Thu Dec  3 10:56:32 EST 2020

% Result     : Theorem 0.53s
% Output     : CNFRefutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  186 (10072 expanded)
%              Number of clauses        :  135 (4757 expanded)
%              Number of leaves         :   25 (2485 expanded)
%              Depth                    :   24
%              Number of atoms          :  492 (34551 expanded)
%              Number of equality atoms :   86 (5244 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t41_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v4_ordinal1(X1)
      <=> ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X2,X1)
             => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).

fof(t34_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,k1_ordinal1(X2))
          <=> r1_ordinal1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(connectedness_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
        | r1_ordinal1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t39_ordinal1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v3_ordinal1(X2)
      & ~ r2_hidden(X2,X1)
      & ! [X3] :
          ( v3_ordinal1(X3)
         => ( ~ r2_hidden(X3,X1)
           => r1_ordinal1(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_ordinal1)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(t35_ordinal1,axiom,(
    ! [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
         => v3_ordinal1(X2) )
     => v3_ordinal1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_ordinal1)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(d6_ordinal1,axiom,(
    ! [X1] :
      ( v4_ordinal1(X1)
    <=> X1 = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_ordinal1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(t14_ordinal1,axiom,(
    ! [X1] : X1 != k1_ordinal1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

fof(t96_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_xboole_0(X1,X2)) = k2_xboole_0(k3_tarski(X1),k3_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(c_0_25,plain,(
    ! [X41] : k1_ordinal1(X41) = k2_xboole_0(X41,k1_tarski(X41)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_26,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ( v4_ordinal1(X1)
        <=> ! [X2] :
              ( v3_ordinal1(X2)
             => ( r2_hidden(X2,X1)
               => r2_hidden(k1_ordinal1(X2),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_ordinal1])).

fof(c_0_28,plain,(
    ! [X58,X59] :
      ( ( ~ r2_hidden(X58,k1_ordinal1(X59))
        | r1_ordinal1(X58,X59)
        | ~ v3_ordinal1(X59)
        | ~ v3_ordinal1(X58) )
      & ( ~ r1_ordinal1(X58,X59)
        | r2_hidden(X58,k1_ordinal1(X59))
        | ~ v3_ordinal1(X59)
        | ~ v3_ordinal1(X58) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).

cnf(c_0_29,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_31,plain,(
    ! [X39,X40] :
      ( ~ v3_ordinal1(X39)
      | ~ v3_ordinal1(X40)
      | r1_ordinal1(X39,X40)
      | r1_ordinal1(X40,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).

fof(c_0_32,negated_conjecture,(
    ! [X69] :
      ( v3_ordinal1(esk8_0)
      & ( v3_ordinal1(esk9_0)
        | ~ v4_ordinal1(esk8_0) )
      & ( r2_hidden(esk9_0,esk8_0)
        | ~ v4_ordinal1(esk8_0) )
      & ( ~ r2_hidden(k1_ordinal1(esk9_0),esk8_0)
        | ~ v4_ordinal1(esk8_0) )
      & ( v4_ordinal1(esk8_0)
        | ~ v3_ordinal1(X69)
        | ~ r2_hidden(X69,esk8_0)
        | r2_hidden(k1_ordinal1(X69),esk8_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])])])).

fof(c_0_33,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X10,X9)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X14)
        | r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k2_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_34,plain,(
    ! [X62,X64] :
      ( v3_ordinal1(esk7_1(X62))
      & ~ r2_hidden(esk7_1(X62),X62)
      & ( ~ v3_ordinal1(X64)
        | r2_hidden(X64,X62)
        | r1_ordinal1(esk7_1(X62),X64) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_ordinal1])])])])])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( r1_ordinal1(X1,X2)
    | r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( v3_ordinal1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_39,plain,(
    ! [X52,X53] :
      ( ~ v3_ordinal1(X53)
      | ~ r2_hidden(X52,X53)
      | v3_ordinal1(X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(esk7_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k2_tarski(X2,X2)))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r1_ordinal1(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( v3_ordinal1(esk7_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( r1_ordinal1(X1,esk8_0)
    | r1_ordinal1(esk8_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_45,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_46,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_40])).

fof(c_0_48,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k2_xboole_0(X18,X19) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_49,plain,(
    ! [X47,X48] :
      ( ( ~ r1_ordinal1(X47,X48)
        | r1_tarski(X47,X48)
        | ~ v3_ordinal1(X47)
        | ~ v3_ordinal1(X48) )
      & ( ~ r1_tarski(X47,X48)
        | r1_ordinal1(X47,X48)
        | ~ v3_ordinal1(X47)
        | ~ v3_ordinal1(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_50,plain,
    ( ~ r1_ordinal1(esk7_1(k2_xboole_0(X1,k2_tarski(X1,X1))),X1)
    | ~ v3_ordinal1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_51,negated_conjecture,
    ( r1_ordinal1(esk8_0,esk7_1(X1))
    | r1_ordinal1(esk7_1(X1),esk8_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_43])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( v3_ordinal1(X1)
    | ~ v3_ordinal1(k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( r1_ordinal1(esk8_0,esk7_1(k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_38])])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(k2_xboole_0(X1,X2),X3)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_47])).

fof(c_0_58,plain,(
    ! [X33,X34] :
      ( ~ r2_hidden(X33,X34)
      | r1_tarski(X33,k3_tarski(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

fof(c_0_59,plain,(
    ! [X22,X23,X24,X26,X27,X28,X29,X31] :
      ( ( r2_hidden(X24,esk2_3(X22,X23,X24))
        | ~ r2_hidden(X24,X23)
        | X23 != k3_tarski(X22) )
      & ( r2_hidden(esk2_3(X22,X23,X24),X22)
        | ~ r2_hidden(X24,X23)
        | X23 != k3_tarski(X22) )
      & ( ~ r2_hidden(X26,X27)
        | ~ r2_hidden(X27,X22)
        | r2_hidden(X26,X23)
        | X23 != k3_tarski(X22) )
      & ( ~ r2_hidden(esk3_2(X28,X29),X29)
        | ~ r2_hidden(esk3_2(X28,X29),X31)
        | ~ r2_hidden(X31,X28)
        | X29 = k3_tarski(X28) )
      & ( r2_hidden(esk3_2(X28,X29),esk4_2(X28,X29))
        | r2_hidden(esk3_2(X28,X29),X29)
        | X29 = k3_tarski(X28) )
      & ( r2_hidden(esk4_2(X28,X29),X28)
        | r2_hidden(esk3_2(X28,X29),X29)
        | X29 = k3_tarski(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

fof(c_0_60,plain,(
    ! [X60] :
      ( ( r2_hidden(esk6_1(X60),X60)
        | v3_ordinal1(k3_tarski(X60)) )
      & ( ~ v3_ordinal1(esk6_1(X60))
        | v3_ordinal1(k3_tarski(X60)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_ordinal1])])])])).

cnf(c_0_61,plain,
    ( v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk8_0,esk7_1(k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_43]),c_0_38])])).

fof(c_0_63,plain,(
    ! [X49,X50] :
      ( ( ~ r2_hidden(X49,k1_ordinal1(X50))
        | r2_hidden(X49,X50)
        | X49 = X50 )
      & ( ~ r2_hidden(X49,X50)
        | r2_hidden(X49,k1_ordinal1(X50)) )
      & ( X49 != X50
        | r2_hidden(X49,k1_ordinal1(X50)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

cnf(c_0_64,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_54])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_67,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_68,plain,(
    ! [X54,X55] :
      ( ~ v3_ordinal1(X54)
      | ~ v3_ordinal1(X55)
      | r2_hidden(X54,X55)
      | X54 = X55
      | r2_hidden(X55,X54) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

cnf(c_0_69,plain,
    ( v3_ordinal1(k3_tarski(X1))
    | ~ v3_ordinal1(esk6_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_43])])).

fof(c_0_71,plain,(
    ! [X65,X66] :
      ( ~ r2_hidden(X65,X66)
      | ~ r1_tarski(X66,X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(k3_tarski(X1),X2)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_66])).

cnf(c_0_75,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_76,plain,(
    ! [X35] : k3_tarski(k1_tarski(X35)) = X35 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_79,negated_conjecture,
    ( v3_ordinal1(k3_tarski(X1))
    | ~ r2_hidden(esk6_1(X1),esk8_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_80,plain,
    ( r2_hidden(esk6_1(X1),X1)
    | v3_ordinal1(k3_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_81,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k2_tarski(X2,X2)))
    | X1 != X2 ),
    inference(rw,[status(thm)],[c_0_72,c_0_36])).

cnf(c_0_83,plain,
    ( ~ r2_hidden(esk2_3(X1,k3_tarski(X1),k3_tarski(X2)),X3)
    | ~ r2_hidden(k3_tarski(X2),k3_tarski(X1))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_84,plain,
    ( r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_75])).

cnf(c_0_85,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_88,negated_conjecture,
    ( v4_ordinal1(esk8_0)
    | r2_hidden(k1_ordinal1(X1),esk8_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_89,negated_conjecture,
    ( X1 = esk8_0
    | r2_hidden(X1,esk8_0)
    | r2_hidden(esk8_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_38])).

cnf(c_0_90,negated_conjecture,
    ( v3_ordinal1(k3_tarski(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_91,plain,
    ( ~ r2_hidden(k3_tarski(X1),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_65])).

cnf(c_0_92,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k2_tarski(X1,X1))) ),
    inference(er,[status(thm)],[c_0_82])).

fof(c_0_93,plain,(
    ! [X46] :
      ( ( ~ v4_ordinal1(X46)
        | X46 = k3_tarski(X46) )
      & ( X46 != k3_tarski(X46)
        | v4_ordinal1(X46) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).

cnf(c_0_94,plain,
    ( ~ r2_hidden(k3_tarski(X1),k3_tarski(X2))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_95,plain,
    ( k3_tarski(k2_tarski(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_85,c_0_30])).

cnf(c_0_96,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_86])).

cnf(c_0_97,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_87])).

fof(c_0_98,plain,(
    ! [X56] :
      ( ~ v3_ordinal1(X56)
      | v3_ordinal1(k1_ordinal1(X56)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

cnf(c_0_99,negated_conjecture,
    ( v4_ordinal1(esk8_0)
    | r2_hidden(k2_xboole_0(X1,k2_tarski(X1,X1)),esk8_0)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(rw,[status(thm)],[c_0_88,c_0_36])).

cnf(c_0_100,negated_conjecture,
    ( k3_tarski(esk8_0) = esk8_0
    | r2_hidden(esk8_0,k3_tarski(esk8_0))
    | r2_hidden(k3_tarski(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_101,plain,
    ( ~ r2_hidden(k2_xboole_0(k3_tarski(X1),k2_tarski(k3_tarski(X1),k3_tarski(X1))),X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_102,plain,
    ( X1 = k3_tarski(X1)
    | ~ v4_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_103,plain,
    ( ~ r2_hidden(X1,k2_tarski(X2,X2))
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_104,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_92]),c_0_97])).

cnf(c_0_105,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_106,negated_conjecture,
    ( v3_ordinal1(esk9_0)
    | ~ v4_ordinal1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_107,plain,
    ( v4_ordinal1(X1)
    | X1 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_108,negated_conjecture,
    ( k3_tarski(esk8_0) = esk8_0
    | r2_hidden(esk8_0,k3_tarski(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_90])]),c_0_101]),c_0_102])).

cnf(c_0_109,plain,
    ( ~ r2_hidden(X1,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_110,plain,
    ( ~ r2_hidden(k2_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_47])).

cnf(c_0_111,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k2_tarski(X1,X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_105,c_0_36])).

cnf(c_0_112,negated_conjecture,
    ( v3_ordinal1(esk9_0)
    | k3_tarski(esk8_0) != esk8_0 ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_113,negated_conjecture,
    ( k3_tarski(esk8_0) = esk8_0 ),
    inference(sr,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_114,plain,
    ( ~ r2_hidden(k2_xboole_0(k2_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_110,c_0_47])).

cnf(c_0_115,plain,
    ( r2_hidden(X1,X2)
    | r1_ordinal1(esk7_1(X2),X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_116,negated_conjecture,
    ( ~ r2_hidden(k1_ordinal1(esk9_0),esk8_0)
    | ~ v4_ordinal1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_117,negated_conjecture,
    ( k2_xboole_0(X1,k2_tarski(X1,X1)) = esk8_0
    | r2_hidden(esk8_0,k2_xboole_0(X1,k2_tarski(X1,X1)))
    | r2_hidden(k2_xboole_0(X1,k2_tarski(X1,X1)),esk8_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_111])).

cnf(c_0_118,negated_conjecture,
    ( v3_ordinal1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_113])])).

cnf(c_0_119,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0)
    | ~ v4_ordinal1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_120,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(k2_xboole_0(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_114,c_0_54])).

cnf(c_0_121,negated_conjecture,
    ( r1_ordinal1(esk7_1(X1),esk8_0)
    | r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_115,c_0_38])).

cnf(c_0_122,negated_conjecture,
    ( ~ v4_ordinal1(esk8_0)
    | ~ r2_hidden(k2_xboole_0(esk9_0,k2_tarski(esk9_0,esk9_0)),esk8_0) ),
    inference(rw,[status(thm)],[c_0_116,c_0_36])).

cnf(c_0_123,negated_conjecture,
    ( k2_xboole_0(esk9_0,k2_tarski(esk9_0,esk9_0)) = esk8_0
    | r2_hidden(k2_xboole_0(esk9_0,k2_tarski(esk9_0,esk9_0)),esk8_0)
    | r2_hidden(esk8_0,k2_xboole_0(esk9_0,k2_tarski(esk9_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0)
    | k3_tarski(esk8_0) != esk8_0 ),
    inference(spm,[status(thm)],[c_0_119,c_0_107])).

cnf(c_0_125,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_120,c_0_54])).

cnf(c_0_126,negated_conjecture,
    ( r1_tarski(esk7_1(X1),esk8_0)
    | r2_hidden(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_121]),c_0_38]),c_0_43])])).

cnf(c_0_127,negated_conjecture,
    ( esk7_1(X1) = esk8_0
    | r2_hidden(esk8_0,esk7_1(X1))
    | r2_hidden(esk7_1(X1),esk8_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_43])).

fof(c_0_128,plain,(
    ! [X51] : X51 != k1_ordinal1(X51) ),
    inference(variable_rename,[status(thm)],[t14_ordinal1])).

cnf(c_0_129,negated_conjecture,
    ( k2_xboole_0(esk9_0,k2_tarski(esk9_0,esk9_0)) = esk8_0
    | r2_hidden(esk8_0,k2_xboole_0(esk9_0,k2_tarski(esk9_0,esk9_0)))
    | ~ v4_ordinal1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_130,negated_conjecture,
    ( r2_hidden(esk9_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_113])])).

cnf(c_0_131,negated_conjecture,
    ( r2_hidden(esk8_0,X1)
    | ~ r1_tarski(esk8_0,X2)
    | ~ r2_hidden(X2,esk7_1(X1)) ),
    inference(spm,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_132,negated_conjecture,
    ( esk7_1(esk8_0) = esk8_0
    | r2_hidden(esk8_0,esk7_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_127])).

cnf(c_0_133,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_134,plain,(
    ! [X36,X37] : k3_tarski(k2_xboole_0(X36,X37)) = k2_xboole_0(k3_tarski(X36),k3_tarski(X37)) ),
    inference(variable_rename,[status(thm)],[t96_zfmisc_1])).

cnf(c_0_135,plain,
    ( X1 != k1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_128])).

cnf(c_0_136,negated_conjecture,
    ( k2_xboole_0(esk9_0,k2_tarski(esk9_0,esk9_0)) = esk8_0
    | r2_hidden(esk8_0,k2_xboole_0(esk9_0,k2_tarski(esk9_0,esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_107]),c_0_113])])).

cnf(c_0_137,negated_conjecture,
    ( ~ r2_hidden(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_130])).

cnf(c_0_138,plain,
    ( r1_ordinal1(esk7_1(X1),esk7_1(X2))
    | r2_hidden(esk7_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_115,c_0_43])).

cnf(c_0_139,negated_conjecture,
    ( esk7_1(esk8_0) = esk8_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_87])]),c_0_97])).

cnf(c_0_140,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_133])).

cnf(c_0_141,plain,
    ( k3_tarski(k2_xboole_0(X1,X2)) = k2_xboole_0(k3_tarski(X1),k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_134])).

fof(c_0_142,plain,(
    ! [X42,X43,X44] :
      ( ( ~ v1_ordinal1(X42)
        | ~ r2_hidden(X43,X42)
        | r1_tarski(X43,X42) )
      & ( r2_hidden(esk5_1(X44),X44)
        | v1_ordinal1(X44) )
      & ( ~ r1_tarski(esk5_1(X44),X44)
        | v1_ordinal1(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

cnf(c_0_143,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_144,plain,
    ( X1 != k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_135,c_0_36])).

cnf(c_0_145,negated_conjecture,
    ( k2_xboole_0(esk9_0,k2_tarski(esk9_0,esk9_0)) = esk8_0
    | r2_hidden(esk8_0,k2_tarski(esk9_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_136]),c_0_137])).

cnf(c_0_146,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_147,negated_conjecture,
    ( r1_ordinal1(esk8_0,esk7_1(X1))
    | r2_hidden(esk7_1(X1),esk8_0) ),
    inference(spm,[status(thm)],[c_0_138,c_0_139])).

cnf(c_0_148,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_130]),c_0_113])).

cnf(c_0_149,plain,
    ( r2_hidden(X1,k3_tarski(k2_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_141])).

cnf(c_0_150,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_142])).

fof(c_0_151,plain,(
    ! [X38] :
      ( ( v1_ordinal1(X38)
        | ~ v3_ordinal1(X38) )
      & ( v2_ordinal1(X38)
        | ~ v3_ordinal1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

cnf(c_0_152,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k2_tarski(X2,X2))) ),
    inference(rw,[status(thm)],[c_0_143,c_0_36])).

cnf(c_0_153,plain,
    ( ~ r2_hidden(X1,k2_tarski(X2,X2))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_95])).

cnf(c_0_154,negated_conjecture,
    ( r2_hidden(esk8_0,k2_tarski(esk9_0,esk9_0))
    | esk9_0 != esk8_0 ),
    inference(spm,[status(thm)],[c_0_144,c_0_145])).

cnf(c_0_155,plain,
    ( ~ r2_hidden(esk7_1(k2_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_47])).

cnf(c_0_156,negated_conjecture,
    ( esk7_1(X1) = esk8_0
    | r2_hidden(esk8_0,X1)
    | ~ r1_tarski(esk8_0,esk7_1(X1)) ),
    inference(spm,[status(thm)],[c_0_146,c_0_126])).

cnf(c_0_157,negated_conjecture,
    ( r1_tarski(esk8_0,esk7_1(X1))
    | r2_hidden(esk7_1(X1),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_147]),c_0_43]),c_0_38])])).

cnf(c_0_158,negated_conjecture,
    ( r1_ordinal1(esk8_0,X1)
    | r2_hidden(X1,esk8_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_115,c_0_139])).

cnf(c_0_159,negated_conjecture,
    ( v3_ordinal1(k3_tarski(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_80]),c_0_79])).

cnf(c_0_160,plain,
    ( ~ r2_hidden(k2_xboole_0(X1,X2),k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_149])).

cnf(c_0_161,negated_conjecture,
    ( r1_tarski(esk9_0,esk8_0)
    | ~ v1_ordinal1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_150,c_0_130])).

cnf(c_0_162,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_151])).

cnf(c_0_163,negated_conjecture,
    ( k2_xboole_0(esk9_0,k2_tarski(esk9_0,esk9_0)) = esk8_0
    | esk9_0 = esk8_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_136]),c_0_137])).

cnf(c_0_164,negated_conjecture,
    ( esk9_0 != esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_154]),c_0_130])])).

cnf(c_0_165,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r2_hidden(X1,k1_ordinal1(X2))
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_166,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(esk7_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_155,c_0_54])).

cnf(c_0_167,negated_conjecture,
    ( esk7_1(X1) = esk8_0
    | r2_hidden(esk7_1(X1),esk8_0)
    | r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_156,c_0_157])).

cnf(c_0_168,negated_conjecture,
    ( r1_ordinal1(esk8_0,k3_tarski(esk9_0))
    | r2_hidden(k3_tarski(esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_158,c_0_159])).

cnf(c_0_169,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_160,c_0_54])).

cnf(c_0_170,negated_conjecture,
    ( r1_tarski(esk9_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_162]),c_0_38])])).

cnf(c_0_171,plain,
    ( k3_tarski(k2_xboole_0(X1,k2_tarski(X2,X2))) = k2_xboole_0(k3_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_141,c_0_95])).

cnf(c_0_172,negated_conjecture,
    ( k2_xboole_0(esk9_0,k2_tarski(esk9_0,esk9_0)) = esk8_0 ),
    inference(sr,[status(thm)],[c_0_163,c_0_164])).

cnf(c_0_173,plain,
    ( r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k2_tarski(X2,X2))) ),
    inference(rw,[status(thm)],[c_0_165,c_0_36])).

cnf(c_0_174,negated_conjecture,
    ( esk7_1(X1) = esk8_0
    | r2_hidden(esk8_0,X1)
    | ~ r1_tarski(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_166,c_0_167])).

cnf(c_0_175,negated_conjecture,
    ( r1_tarski(esk8_0,k3_tarski(esk9_0))
    | r2_hidden(k3_tarski(esk9_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_168]),c_0_159]),c_0_38])])).

cnf(c_0_176,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k3_tarski(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_169,c_0_170])).

cnf(c_0_177,negated_conjecture,
    ( k2_xboole_0(k3_tarski(esk9_0),esk9_0) = esk8_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_172]),c_0_113])).

cnf(c_0_178,negated_conjecture,
    ( r1_ordinal1(X1,esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_172]),c_0_118])]),c_0_70])).

cnf(c_0_179,negated_conjecture,
    ( r1_ordinal1(esk7_1(X1),esk9_0)
    | r2_hidden(esk9_0,X1) ),
    inference(spm,[status(thm)],[c_0_115,c_0_118])).

cnf(c_0_180,negated_conjecture,
    ( esk7_1(k3_tarski(esk9_0)) = esk8_0
    | r2_hidden(k3_tarski(esk9_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_175]),c_0_176])).

cnf(c_0_181,negated_conjecture,
    ( ~ r1_ordinal1(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_172]),c_0_139]),c_0_118])])).

cnf(c_0_182,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(esk9_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_177]),c_0_164])).

cnf(c_0_183,negated_conjecture,
    ( r1_tarski(X1,esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_178]),c_0_118])]),c_0_70])).

cnf(c_0_184,negated_conjecture,
    ( r2_hidden(k3_tarski(esk9_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_180]),c_0_181]),c_0_109])).

cnf(c_0_185,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_182,c_0_183]),c_0_184])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:26:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.53/0.72  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.53/0.72  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.53/0.72  #
% 0.53/0.72  # Preprocessing time       : 0.030 s
% 0.53/0.72  # Presaturation interreduction done
% 0.53/0.72  
% 0.53/0.72  # Proof found!
% 0.53/0.72  # SZS status Theorem
% 0.53/0.72  # SZS output start CNFRefutation
% 0.53/0.72  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.53/0.72  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.53/0.72  fof(t41_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_ordinal1)).
% 0.53/0.72  fof(t34_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,k1_ordinal1(X2))<=>r1_ordinal1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 0.53/0.72  fof(connectedness_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 0.53/0.72  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.53/0.72  fof(t39_ordinal1, axiom, ![X1]:?[X2]:((v3_ordinal1(X2)&~(r2_hidden(X2,X1)))&![X3]:(v3_ordinal1(X3)=>(~(r2_hidden(X3,X1))=>r1_ordinal1(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_ordinal1)).
% 0.53/0.72  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 0.53/0.72  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.53/0.72  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.53/0.72  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.53/0.72  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.53/0.72  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 0.53/0.72  fof(t35_ordinal1, axiom, ![X1]:(![X2]:(r2_hidden(X2,X1)=>v3_ordinal1(X2))=>v3_ordinal1(k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_ordinal1)).
% 0.53/0.72  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 0.53/0.72  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.53/0.72  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 0.53/0.72  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.53/0.72  fof(t31_zfmisc_1, axiom, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 0.53/0.72  fof(d6_ordinal1, axiom, ![X1]:(v4_ordinal1(X1)<=>X1=k3_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_ordinal1)).
% 0.53/0.72  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 0.53/0.72  fof(t14_ordinal1, axiom, ![X1]:X1!=k1_ordinal1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_ordinal1)).
% 0.53/0.72  fof(t96_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_xboole_0(X1,X2))=k2_xboole_0(k3_tarski(X1),k3_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 0.53/0.72  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 0.53/0.72  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 0.53/0.72  fof(c_0_25, plain, ![X41]:k1_ordinal1(X41)=k2_xboole_0(X41,k1_tarski(X41)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.53/0.72  fof(c_0_26, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.53/0.72  fof(c_0_27, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>(v4_ordinal1(X1)<=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X2,X1)=>r2_hidden(k1_ordinal1(X2),X1)))))), inference(assume_negation,[status(cth)],[t41_ordinal1])).
% 0.53/0.72  fof(c_0_28, plain, ![X58, X59]:((~r2_hidden(X58,k1_ordinal1(X59))|r1_ordinal1(X58,X59)|~v3_ordinal1(X59)|~v3_ordinal1(X58))&(~r1_ordinal1(X58,X59)|r2_hidden(X58,k1_ordinal1(X59))|~v3_ordinal1(X59)|~v3_ordinal1(X58))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_ordinal1])])])])).
% 0.53/0.72  cnf(c_0_29, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.53/0.72  cnf(c_0_30, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.53/0.72  fof(c_0_31, plain, ![X39, X40]:(~v3_ordinal1(X39)|~v3_ordinal1(X40)|(r1_ordinal1(X39,X40)|r1_ordinal1(X40,X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).
% 0.53/0.72  fof(c_0_32, negated_conjecture, ![X69]:(v3_ordinal1(esk8_0)&(((v3_ordinal1(esk9_0)|~v4_ordinal1(esk8_0))&((r2_hidden(esk9_0,esk8_0)|~v4_ordinal1(esk8_0))&(~r2_hidden(k1_ordinal1(esk9_0),esk8_0)|~v4_ordinal1(esk8_0))))&(v4_ordinal1(esk8_0)|(~v3_ordinal1(X69)|(~r2_hidden(X69,esk8_0)|r2_hidden(k1_ordinal1(X69),esk8_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])])])).
% 0.53/0.72  fof(c_0_33, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X10,X9)|(r2_hidden(X10,X7)|r2_hidden(X10,X8))|X9!=k2_xboole_0(X7,X8))&((~r2_hidden(X11,X7)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))&(~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))))&(((~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13)))&(r2_hidden(esk1_3(X12,X13,X14),X14)|(r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k2_xboole_0(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.53/0.72  fof(c_0_34, plain, ![X62, X64]:((v3_ordinal1(esk7_1(X62))&~r2_hidden(esk7_1(X62),X62))&(~v3_ordinal1(X64)|(r2_hidden(X64,X62)|r1_ordinal1(esk7_1(X62),X64)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_ordinal1])])])])])).
% 0.53/0.72  cnf(c_0_35, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.53/0.72  cnf(c_0_36, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.53/0.72  cnf(c_0_37, plain, (r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.53/0.72  cnf(c_0_38, negated_conjecture, (v3_ordinal1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.53/0.72  fof(c_0_39, plain, ![X52, X53]:(~v3_ordinal1(X53)|(~r2_hidden(X52,X53)|v3_ordinal1(X52))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 0.53/0.72  cnf(c_0_40, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.53/0.72  cnf(c_0_41, plain, (~r2_hidden(esk7_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.53/0.72  cnf(c_0_42, plain, (r2_hidden(X1,k2_xboole_0(X2,k2_tarski(X2,X2)))|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r1_ordinal1(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.53/0.72  cnf(c_0_43, plain, (v3_ordinal1(esk7_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.53/0.72  cnf(c_0_44, negated_conjecture, (r1_ordinal1(X1,esk8_0)|r1_ordinal1(esk8_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.53/0.72  fof(c_0_45, plain, ![X5, X6]:(~r2_hidden(X5,X6)|~r2_hidden(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.53/0.72  cnf(c_0_46, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.53/0.72  cnf(c_0_47, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_40])).
% 0.53/0.72  fof(c_0_48, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k2_xboole_0(X18,X19)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.53/0.72  fof(c_0_49, plain, ![X47, X48]:((~r1_ordinal1(X47,X48)|r1_tarski(X47,X48)|(~v3_ordinal1(X47)|~v3_ordinal1(X48)))&(~r1_tarski(X47,X48)|r1_ordinal1(X47,X48)|(~v3_ordinal1(X47)|~v3_ordinal1(X48)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.53/0.72  cnf(c_0_50, plain, (~r1_ordinal1(esk7_1(k2_xboole_0(X1,k2_tarski(X1,X1))),X1)|~v3_ordinal1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])])).
% 0.53/0.72  cnf(c_0_51, negated_conjecture, (r1_ordinal1(esk8_0,esk7_1(X1))|r1_ordinal1(esk7_1(X1),esk8_0)), inference(spm,[status(thm)],[c_0_44, c_0_43])).
% 0.53/0.72  cnf(c_0_52, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.53/0.72  cnf(c_0_53, plain, (v3_ordinal1(X1)|~v3_ordinal1(k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.53/0.72  cnf(c_0_54, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.53/0.72  cnf(c_0_55, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.53/0.72  cnf(c_0_56, negated_conjecture, (r1_ordinal1(esk8_0,esk7_1(k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_38])])).
% 0.53/0.72  cnf(c_0_57, plain, (~r2_hidden(k2_xboole_0(X1,X2),X3)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_52, c_0_47])).
% 0.53/0.72  fof(c_0_58, plain, ![X33, X34]:(~r2_hidden(X33,X34)|r1_tarski(X33,k3_tarski(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.53/0.72  fof(c_0_59, plain, ![X22, X23, X24, X26, X27, X28, X29, X31]:((((r2_hidden(X24,esk2_3(X22,X23,X24))|~r2_hidden(X24,X23)|X23!=k3_tarski(X22))&(r2_hidden(esk2_3(X22,X23,X24),X22)|~r2_hidden(X24,X23)|X23!=k3_tarski(X22)))&(~r2_hidden(X26,X27)|~r2_hidden(X27,X22)|r2_hidden(X26,X23)|X23!=k3_tarski(X22)))&((~r2_hidden(esk3_2(X28,X29),X29)|(~r2_hidden(esk3_2(X28,X29),X31)|~r2_hidden(X31,X28))|X29=k3_tarski(X28))&((r2_hidden(esk3_2(X28,X29),esk4_2(X28,X29))|r2_hidden(esk3_2(X28,X29),X29)|X29=k3_tarski(X28))&(r2_hidden(esk4_2(X28,X29),X28)|r2_hidden(esk3_2(X28,X29),X29)|X29=k3_tarski(X28))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.53/0.72  fof(c_0_60, plain, ![X60]:((r2_hidden(esk6_1(X60),X60)|v3_ordinal1(k3_tarski(X60)))&(~v3_ordinal1(esk6_1(X60))|v3_ordinal1(k3_tarski(X60)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_ordinal1])])])])).
% 0.53/0.72  cnf(c_0_61, plain, (v3_ordinal1(X1)|~v3_ordinal1(X2)|~r1_tarski(X3,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.53/0.72  cnf(c_0_62, negated_conjecture, (r1_tarski(esk8_0,esk7_1(k2_xboole_0(esk8_0,k2_tarski(esk8_0,esk8_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_43]), c_0_38])])).
% 0.53/0.72  fof(c_0_63, plain, ![X49, X50]:((~r2_hidden(X49,k1_ordinal1(X50))|(r2_hidden(X49,X50)|X49=X50))&((~r2_hidden(X49,X50)|r2_hidden(X49,k1_ordinal1(X50)))&(X49!=X50|r2_hidden(X49,k1_ordinal1(X50))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 0.53/0.72  cnf(c_0_64, plain, (~r1_tarski(X1,X2)|~r2_hidden(X2,X3)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_57, c_0_54])).
% 0.53/0.72  cnf(c_0_65, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.53/0.72  cnf(c_0_66, plain, (r2_hidden(X1,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k3_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.53/0.72  fof(c_0_67, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.53/0.72  fof(c_0_68, plain, ![X54, X55]:(~v3_ordinal1(X54)|(~v3_ordinal1(X55)|(r2_hidden(X54,X55)|X54=X55|r2_hidden(X55,X54)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 0.53/0.72  cnf(c_0_69, plain, (v3_ordinal1(k3_tarski(X1))|~v3_ordinal1(esk6_1(X1))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.53/0.72  cnf(c_0_70, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_43])])).
% 0.53/0.72  fof(c_0_71, plain, ![X65, X66]:(~r2_hidden(X65,X66)|~r1_tarski(X66,X65)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.53/0.72  cnf(c_0_72, plain, (r2_hidden(X1,k1_ordinal1(X2))|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.53/0.72  cnf(c_0_73, plain, (~r2_hidden(k3_tarski(X1),X2)|~r2_hidden(X2,X3)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.53/0.72  cnf(c_0_74, plain, (r2_hidden(X1,esk2_3(X2,k3_tarski(X2),X1))|~r2_hidden(X1,k3_tarski(X2))), inference(er,[status(thm)],[c_0_66])).
% 0.53/0.72  cnf(c_0_75, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.53/0.72  fof(c_0_76, plain, ![X35]:k3_tarski(k1_tarski(X35))=X35, inference(variable_rename,[status(thm)],[t31_zfmisc_1])).
% 0.53/0.72  cnf(c_0_77, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.53/0.72  cnf(c_0_78, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.53/0.72  cnf(c_0_79, negated_conjecture, (v3_ordinal1(k3_tarski(X1))|~r2_hidden(esk6_1(X1),esk8_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.53/0.72  cnf(c_0_80, plain, (r2_hidden(esk6_1(X1),X1)|v3_ordinal1(k3_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.53/0.72  cnf(c_0_81, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.53/0.72  cnf(c_0_82, plain, (r2_hidden(X1,k2_xboole_0(X2,k2_tarski(X2,X2)))|X1!=X2), inference(rw,[status(thm)],[c_0_72, c_0_36])).
% 0.53/0.72  cnf(c_0_83, plain, (~r2_hidden(esk2_3(X1,k3_tarski(X1),k3_tarski(X2)),X3)|~r2_hidden(k3_tarski(X2),k3_tarski(X1))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.53/0.72  cnf(c_0_84, plain, (r2_hidden(esk2_3(X1,k3_tarski(X1),X2),X1)|~r2_hidden(X2,k3_tarski(X1))), inference(er,[status(thm)],[c_0_75])).
% 0.53/0.72  cnf(c_0_85, plain, (k3_tarski(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.53/0.72  cnf(c_0_86, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.53/0.72  cnf(c_0_87, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_77])).
% 0.53/0.72  cnf(c_0_88, negated_conjecture, (v4_ordinal1(esk8_0)|r2_hidden(k1_ordinal1(X1),esk8_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.53/0.72  cnf(c_0_89, negated_conjecture, (X1=esk8_0|r2_hidden(X1,esk8_0)|r2_hidden(esk8_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_78, c_0_38])).
% 0.53/0.72  cnf(c_0_90, negated_conjecture, (v3_ordinal1(k3_tarski(esk8_0))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.53/0.72  cnf(c_0_91, plain, (~r2_hidden(k3_tarski(X1),X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_81, c_0_65])).
% 0.53/0.72  cnf(c_0_92, plain, (r2_hidden(X1,k2_xboole_0(X1,k2_tarski(X1,X1)))), inference(er,[status(thm)],[c_0_82])).
% 0.53/0.72  fof(c_0_93, plain, ![X46]:((~v4_ordinal1(X46)|X46=k3_tarski(X46))&(X46!=k3_tarski(X46)|v4_ordinal1(X46))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_ordinal1])])).
% 0.53/0.72  cnf(c_0_94, plain, (~r2_hidden(k3_tarski(X1),k3_tarski(X2))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.53/0.72  cnf(c_0_95, plain, (k3_tarski(k2_tarski(X1,X1))=X1), inference(rw,[status(thm)],[c_0_85, c_0_30])).
% 0.53/0.72  cnf(c_0_96, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_86])).
% 0.53/0.72  cnf(c_0_97, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_81, c_0_87])).
% 0.53/0.72  fof(c_0_98, plain, ![X56]:(~v3_ordinal1(X56)|v3_ordinal1(k1_ordinal1(X56))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 0.53/0.72  cnf(c_0_99, negated_conjecture, (v4_ordinal1(esk8_0)|r2_hidden(k2_xboole_0(X1,k2_tarski(X1,X1)),esk8_0)|~v3_ordinal1(X1)|~r2_hidden(X1,esk8_0)), inference(rw,[status(thm)],[c_0_88, c_0_36])).
% 0.53/0.72  cnf(c_0_100, negated_conjecture, (k3_tarski(esk8_0)=esk8_0|r2_hidden(esk8_0,k3_tarski(esk8_0))|r2_hidden(k3_tarski(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.53/0.72  cnf(c_0_101, plain, (~r2_hidden(k2_xboole_0(k3_tarski(X1),k2_tarski(k3_tarski(X1),k3_tarski(X1))),X1)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.53/0.72  cnf(c_0_102, plain, (X1=k3_tarski(X1)|~v4_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.53/0.72  cnf(c_0_103, plain, (~r2_hidden(X1,k2_tarski(X2,X2))|~r2_hidden(X2,k3_tarski(X1))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.53/0.72  cnf(c_0_104, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_92]), c_0_97])).
% 0.53/0.72  cnf(c_0_105, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.53/0.72  cnf(c_0_106, negated_conjecture, (v3_ordinal1(esk9_0)|~v4_ordinal1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.53/0.72  cnf(c_0_107, plain, (v4_ordinal1(X1)|X1!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.53/0.72  cnf(c_0_108, negated_conjecture, (k3_tarski(esk8_0)=esk8_0|r2_hidden(esk8_0,k3_tarski(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_90])]), c_0_101]), c_0_102])).
% 0.53/0.72  cnf(c_0_109, plain, (~r2_hidden(X1,k3_tarski(X1))), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.53/0.72  cnf(c_0_110, plain, (~r2_hidden(k2_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_97, c_0_47])).
% 0.53/0.72  cnf(c_0_111, plain, (v3_ordinal1(k2_xboole_0(X1,k2_tarski(X1,X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_105, c_0_36])).
% 0.53/0.72  cnf(c_0_112, negated_conjecture, (v3_ordinal1(esk9_0)|k3_tarski(esk8_0)!=esk8_0), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 0.53/0.72  cnf(c_0_113, negated_conjecture, (k3_tarski(esk8_0)=esk8_0), inference(sr,[status(thm)],[c_0_108, c_0_109])).
% 0.53/0.72  cnf(c_0_114, plain, (~r2_hidden(k2_xboole_0(k2_xboole_0(X1,X2),X3),X1)), inference(spm,[status(thm)],[c_0_110, c_0_47])).
% 0.53/0.72  cnf(c_0_115, plain, (r2_hidden(X1,X2)|r1_ordinal1(esk7_1(X2),X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.53/0.72  cnf(c_0_116, negated_conjecture, (~r2_hidden(k1_ordinal1(esk9_0),esk8_0)|~v4_ordinal1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.53/0.72  cnf(c_0_117, negated_conjecture, (k2_xboole_0(X1,k2_tarski(X1,X1))=esk8_0|r2_hidden(esk8_0,k2_xboole_0(X1,k2_tarski(X1,X1)))|r2_hidden(k2_xboole_0(X1,k2_tarski(X1,X1)),esk8_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_89, c_0_111])).
% 0.53/0.72  cnf(c_0_118, negated_conjecture, (v3_ordinal1(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_113])])).
% 0.53/0.72  cnf(c_0_119, negated_conjecture, (r2_hidden(esk9_0,esk8_0)|~v4_ordinal1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.53/0.72  cnf(c_0_120, plain, (~r1_tarski(X1,X2)|~r2_hidden(k2_xboole_0(X2,X3),X1)), inference(spm,[status(thm)],[c_0_114, c_0_54])).
% 0.53/0.72  cnf(c_0_121, negated_conjecture, (r1_ordinal1(esk7_1(X1),esk8_0)|r2_hidden(esk8_0,X1)), inference(spm,[status(thm)],[c_0_115, c_0_38])).
% 0.53/0.72  cnf(c_0_122, negated_conjecture, (~v4_ordinal1(esk8_0)|~r2_hidden(k2_xboole_0(esk9_0,k2_tarski(esk9_0,esk9_0)),esk8_0)), inference(rw,[status(thm)],[c_0_116, c_0_36])).
% 0.53/0.72  cnf(c_0_123, negated_conjecture, (k2_xboole_0(esk9_0,k2_tarski(esk9_0,esk9_0))=esk8_0|r2_hidden(k2_xboole_0(esk9_0,k2_tarski(esk9_0,esk9_0)),esk8_0)|r2_hidden(esk8_0,k2_xboole_0(esk9_0,k2_tarski(esk9_0,esk9_0)))), inference(spm,[status(thm)],[c_0_117, c_0_118])).
% 0.53/0.72  cnf(c_0_124, negated_conjecture, (r2_hidden(esk9_0,esk8_0)|k3_tarski(esk8_0)!=esk8_0), inference(spm,[status(thm)],[c_0_119, c_0_107])).
% 0.53/0.72  cnf(c_0_125, plain, (~r1_tarski(X1,X2)|~r1_tarski(X2,X3)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_120, c_0_54])).
% 0.53/0.72  cnf(c_0_126, negated_conjecture, (r1_tarski(esk7_1(X1),esk8_0)|r2_hidden(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_121]), c_0_38]), c_0_43])])).
% 0.53/0.72  cnf(c_0_127, negated_conjecture, (esk7_1(X1)=esk8_0|r2_hidden(esk8_0,esk7_1(X1))|r2_hidden(esk7_1(X1),esk8_0)), inference(spm,[status(thm)],[c_0_89, c_0_43])).
% 0.53/0.72  fof(c_0_128, plain, ![X51]:X51!=k1_ordinal1(X51), inference(variable_rename,[status(thm)],[t14_ordinal1])).
% 0.53/0.72  cnf(c_0_129, negated_conjecture, (k2_xboole_0(esk9_0,k2_tarski(esk9_0,esk9_0))=esk8_0|r2_hidden(esk8_0,k2_xboole_0(esk9_0,k2_tarski(esk9_0,esk9_0)))|~v4_ordinal1(esk8_0)), inference(spm,[status(thm)],[c_0_122, c_0_123])).
% 0.53/0.72  cnf(c_0_130, negated_conjecture, (r2_hidden(esk9_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_113])])).
% 0.53/0.72  cnf(c_0_131, negated_conjecture, (r2_hidden(esk8_0,X1)|~r1_tarski(esk8_0,X2)|~r2_hidden(X2,esk7_1(X1))), inference(spm,[status(thm)],[c_0_125, c_0_126])).
% 0.53/0.72  cnf(c_0_132, negated_conjecture, (esk7_1(esk8_0)=esk8_0|r2_hidden(esk8_0,esk7_1(esk8_0))), inference(spm,[status(thm)],[c_0_41, c_0_127])).
% 0.53/0.72  cnf(c_0_133, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.53/0.72  fof(c_0_134, plain, ![X36, X37]:k3_tarski(k2_xboole_0(X36,X37))=k2_xboole_0(k3_tarski(X36),k3_tarski(X37)), inference(variable_rename,[status(thm)],[t96_zfmisc_1])).
% 0.53/0.72  cnf(c_0_135, plain, (X1!=k1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_128])).
% 0.53/0.72  cnf(c_0_136, negated_conjecture, (k2_xboole_0(esk9_0,k2_tarski(esk9_0,esk9_0))=esk8_0|r2_hidden(esk8_0,k2_xboole_0(esk9_0,k2_tarski(esk9_0,esk9_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_107]), c_0_113])])).
% 0.53/0.72  cnf(c_0_137, negated_conjecture, (~r2_hidden(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_52, c_0_130])).
% 0.53/0.72  cnf(c_0_138, plain, (r1_ordinal1(esk7_1(X1),esk7_1(X2))|r2_hidden(esk7_1(X2),X1)), inference(spm,[status(thm)],[c_0_115, c_0_43])).
% 0.53/0.72  cnf(c_0_139, negated_conjecture, (esk7_1(esk8_0)=esk8_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_87])]), c_0_97])).
% 0.53/0.72  cnf(c_0_140, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_133])).
% 0.53/0.72  cnf(c_0_141, plain, (k3_tarski(k2_xboole_0(X1,X2))=k2_xboole_0(k3_tarski(X1),k3_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_134])).
% 0.53/0.72  fof(c_0_142, plain, ![X42, X43, X44]:((~v1_ordinal1(X42)|(~r2_hidden(X43,X42)|r1_tarski(X43,X42)))&((r2_hidden(esk5_1(X44),X44)|v1_ordinal1(X44))&(~r1_tarski(esk5_1(X44),X44)|v1_ordinal1(X44)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 0.53/0.72  cnf(c_0_143, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.53/0.72  cnf(c_0_144, plain, (X1!=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_135, c_0_36])).
% 0.53/0.72  cnf(c_0_145, negated_conjecture, (k2_xboole_0(esk9_0,k2_tarski(esk9_0,esk9_0))=esk8_0|r2_hidden(esk8_0,k2_tarski(esk9_0,esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_136]), c_0_137])).
% 0.53/0.72  cnf(c_0_146, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.53/0.72  cnf(c_0_147, negated_conjecture, (r1_ordinal1(esk8_0,esk7_1(X1))|r2_hidden(esk7_1(X1),esk8_0)), inference(spm,[status(thm)],[c_0_138, c_0_139])).
% 0.53/0.72  cnf(c_0_148, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(X1,esk9_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_130]), c_0_113])).
% 0.53/0.72  cnf(c_0_149, plain, (r2_hidden(X1,k3_tarski(k2_xboole_0(X2,X3)))|~r2_hidden(X1,k3_tarski(X2))), inference(spm,[status(thm)],[c_0_47, c_0_141])).
% 0.53/0.72  cnf(c_0_150, plain, (r1_tarski(X2,X1)|~v1_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_142])).
% 0.53/0.72  fof(c_0_151, plain, ![X38]:((v1_ordinal1(X38)|~v3_ordinal1(X38))&(v2_ordinal1(X38)|~v3_ordinal1(X38))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 0.53/0.72  cnf(c_0_152, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k2_xboole_0(X2,k2_tarski(X2,X2)))), inference(rw,[status(thm)],[c_0_143, c_0_36])).
% 0.53/0.72  cnf(c_0_153, plain, (~r2_hidden(X1,k2_tarski(X2,X2))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_91, c_0_95])).
% 0.53/0.72  cnf(c_0_154, negated_conjecture, (r2_hidden(esk8_0,k2_tarski(esk9_0,esk9_0))|esk9_0!=esk8_0), inference(spm,[status(thm)],[c_0_144, c_0_145])).
% 0.53/0.72  cnf(c_0_155, plain, (~r2_hidden(esk7_1(k2_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_41, c_0_47])).
% 0.53/0.72  cnf(c_0_156, negated_conjecture, (esk7_1(X1)=esk8_0|r2_hidden(esk8_0,X1)|~r1_tarski(esk8_0,esk7_1(X1))), inference(spm,[status(thm)],[c_0_146, c_0_126])).
% 0.53/0.72  cnf(c_0_157, negated_conjecture, (r1_tarski(esk8_0,esk7_1(X1))|r2_hidden(esk7_1(X1),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_147]), c_0_43]), c_0_38])])).
% 0.53/0.72  cnf(c_0_158, negated_conjecture, (r1_ordinal1(esk8_0,X1)|r2_hidden(X1,esk8_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_115, c_0_139])).
% 0.53/0.72  cnf(c_0_159, negated_conjecture, (v3_ordinal1(k3_tarski(esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_80]), c_0_79])).
% 0.53/0.72  cnf(c_0_160, plain, (~r2_hidden(k2_xboole_0(X1,X2),k3_tarski(X1))), inference(spm,[status(thm)],[c_0_109, c_0_149])).
% 0.53/0.72  cnf(c_0_161, negated_conjecture, (r1_tarski(esk9_0,esk8_0)|~v1_ordinal1(esk8_0)), inference(spm,[status(thm)],[c_0_150, c_0_130])).
% 0.53/0.72  cnf(c_0_162, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_151])).
% 0.53/0.72  cnf(c_0_163, negated_conjecture, (k2_xboole_0(esk9_0,k2_tarski(esk9_0,esk9_0))=esk8_0|esk9_0=esk8_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_136]), c_0_137])).
% 0.53/0.72  cnf(c_0_164, negated_conjecture, (esk9_0!=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_154]), c_0_130])])).
% 0.53/0.72  cnf(c_0_165, plain, (r1_ordinal1(X1,X2)|~r2_hidden(X1,k1_ordinal1(X2))|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.53/0.72  cnf(c_0_166, plain, (~r1_tarski(X1,X2)|~r2_hidden(esk7_1(X2),X1)), inference(spm,[status(thm)],[c_0_155, c_0_54])).
% 0.53/0.72  cnf(c_0_167, negated_conjecture, (esk7_1(X1)=esk8_0|r2_hidden(esk7_1(X1),esk8_0)|r2_hidden(esk8_0,X1)), inference(spm,[status(thm)],[c_0_156, c_0_157])).
% 0.53/0.72  cnf(c_0_168, negated_conjecture, (r1_ordinal1(esk8_0,k3_tarski(esk9_0))|r2_hidden(k3_tarski(esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_158, c_0_159])).
% 0.53/0.72  cnf(c_0_169, plain, (~r1_tarski(X1,X2)|~r2_hidden(X2,k3_tarski(X1))), inference(spm,[status(thm)],[c_0_160, c_0_54])).
% 0.53/0.72  cnf(c_0_170, negated_conjecture, (r1_tarski(esk9_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161, c_0_162]), c_0_38])])).
% 0.53/0.72  cnf(c_0_171, plain, (k3_tarski(k2_xboole_0(X1,k2_tarski(X2,X2)))=k2_xboole_0(k3_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_141, c_0_95])).
% 0.53/0.72  cnf(c_0_172, negated_conjecture, (k2_xboole_0(esk9_0,k2_tarski(esk9_0,esk9_0))=esk8_0), inference(sr,[status(thm)],[c_0_163, c_0_164])).
% 0.53/0.72  cnf(c_0_173, plain, (r1_ordinal1(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X1,k2_xboole_0(X2,k2_tarski(X2,X2)))), inference(rw,[status(thm)],[c_0_165, c_0_36])).
% 0.53/0.72  cnf(c_0_174, negated_conjecture, (esk7_1(X1)=esk8_0|r2_hidden(esk8_0,X1)|~r1_tarski(esk8_0,X1)), inference(spm,[status(thm)],[c_0_166, c_0_167])).
% 0.53/0.72  cnf(c_0_175, negated_conjecture, (r1_tarski(esk8_0,k3_tarski(esk9_0))|r2_hidden(k3_tarski(esk9_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_168]), c_0_159]), c_0_38])])).
% 0.53/0.72  cnf(c_0_176, negated_conjecture, (~r2_hidden(esk8_0,k3_tarski(esk9_0))), inference(spm,[status(thm)],[c_0_169, c_0_170])).
% 0.53/0.72  cnf(c_0_177, negated_conjecture, (k2_xboole_0(k3_tarski(esk9_0),esk9_0)=esk8_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_172]), c_0_113])).
% 0.53/0.72  cnf(c_0_178, negated_conjecture, (r1_ordinal1(X1,esk9_0)|~r2_hidden(X1,esk8_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173, c_0_172]), c_0_118])]), c_0_70])).
% 0.53/0.72  cnf(c_0_179, negated_conjecture, (r1_ordinal1(esk7_1(X1),esk9_0)|r2_hidden(esk9_0,X1)), inference(spm,[status(thm)],[c_0_115, c_0_118])).
% 0.53/0.72  cnf(c_0_180, negated_conjecture, (esk7_1(k3_tarski(esk9_0))=esk8_0|r2_hidden(k3_tarski(esk9_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_174, c_0_175]), c_0_176])).
% 0.53/0.72  cnf(c_0_181, negated_conjecture, (~r1_ordinal1(esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_172]), c_0_139]), c_0_118])])).
% 0.53/0.72  cnf(c_0_182, negated_conjecture, (~r1_tarski(k3_tarski(esk9_0),esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_177]), c_0_164])).
% 0.53/0.72  cnf(c_0_183, negated_conjecture, (r1_tarski(X1,esk9_0)|~r2_hidden(X1,esk8_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_178]), c_0_118])]), c_0_70])).
% 0.53/0.72  cnf(c_0_184, negated_conjecture, (r2_hidden(k3_tarski(esk9_0),esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_179, c_0_180]), c_0_181]), c_0_109])).
% 0.53/0.72  cnf(c_0_185, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_182, c_0_183]), c_0_184])]), ['proof']).
% 0.53/0.72  # SZS output end CNFRefutation
% 0.53/0.72  # Proof object total steps             : 186
% 0.53/0.72  # Proof object clause steps            : 135
% 0.53/0.72  # Proof object formula steps           : 51
% 0.53/0.72  # Proof object conjectures             : 63
% 0.53/0.72  # Proof object clause conjectures      : 60
% 0.53/0.72  # Proof object formula conjectures     : 3
% 0.53/0.72  # Proof object initial clauses used    : 39
% 0.53/0.72  # Proof object initial formulas used   : 25
% 0.53/0.72  # Proof object generating inferences   : 75
% 0.53/0.72  # Proof object simplifying inferences  : 75
% 0.53/0.72  # Training examples: 0 positive, 0 negative
% 0.53/0.72  # Parsed axioms                        : 27
% 0.53/0.72  # Removed by relevancy pruning/SinE    : 0
% 0.53/0.72  # Initial clauses                      : 54
% 0.53/0.72  # Removed in clause preprocessing      : 2
% 0.53/0.72  # Initial clauses in saturation        : 52
% 0.53/0.72  # Processed clauses                    : 4957
% 0.53/0.72  # ...of these trivial                  : 34
% 0.53/0.72  # ...subsumed                          : 3394
% 0.53/0.72  # ...remaining for further processing  : 1529
% 0.53/0.72  # Other redundant clauses eliminated   : 9
% 0.53/0.72  # Clauses deleted for lack of memory   : 0
% 0.53/0.72  # Backward-subsumed                    : 61
% 0.53/0.72  # Backward-rewritten                   : 205
% 0.53/0.72  # Generated clauses                    : 22607
% 0.53/0.72  # ...of the previous two non-trivial   : 20909
% 0.53/0.72  # Contextual simplify-reflections      : 26
% 0.53/0.72  # Paramodulations                      : 22443
% 0.53/0.72  # Factorizations                       : 150
% 0.53/0.72  # Equation resolutions                 : 9
% 0.53/0.72  # Propositional unsat checks           : 0
% 0.53/0.72  #    Propositional check models        : 0
% 0.53/0.72  #    Propositional check unsatisfiable : 0
% 0.53/0.72  #    Propositional clauses             : 0
% 0.53/0.72  #    Propositional clauses after purity: 0
% 0.53/0.72  #    Propositional unsat core size     : 0
% 0.53/0.72  #    Propositional preprocessing time  : 0.000
% 0.53/0.72  #    Propositional encoding time       : 0.000
% 0.53/0.72  #    Propositional solver time         : 0.000
% 0.53/0.72  #    Success case prop preproc time    : 0.000
% 0.53/0.72  #    Success case prop encoding time   : 0.000
% 0.53/0.72  #    Success case prop solver time     : 0.000
% 0.53/0.72  # Current number of processed clauses  : 1199
% 0.53/0.72  #    Positive orientable unit clauses  : 112
% 0.53/0.72  #    Positive unorientable unit clauses: 0
% 0.53/0.72  #    Negative unit clauses             : 281
% 0.53/0.72  #    Non-unit-clauses                  : 806
% 0.53/0.72  # Current number of unprocessed clauses: 15488
% 0.53/0.72  # ...number of literals in the above   : 48847
% 0.53/0.72  # Current number of archived formulas  : 0
% 0.53/0.72  # Current number of archived clauses   : 323
% 0.53/0.72  # Clause-clause subsumption calls (NU) : 76466
% 0.53/0.72  # Rec. Clause-clause subsumption calls : 48022
% 0.53/0.72  # Non-unit clause-clause subsumptions  : 1183
% 0.53/0.72  # Unit Clause-clause subsumption calls : 16835
% 0.53/0.72  # Rewrite failures with RHS unbound    : 0
% 0.53/0.72  # BW rewrite match attempts            : 225
% 0.53/0.72  # BW rewrite match successes           : 35
% 0.53/0.72  # Condensation attempts                : 0
% 0.53/0.72  # Condensation successes               : 0
% 0.53/0.72  # Termbank termtop insertions          : 311992
% 0.53/0.72  
% 0.53/0.72  # -------------------------------------------------
% 0.53/0.72  # User time                : 0.352 s
% 0.53/0.72  # System time              : 0.020 s
% 0.53/0.72  # Total time               : 0.371 s
% 0.53/0.72  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
