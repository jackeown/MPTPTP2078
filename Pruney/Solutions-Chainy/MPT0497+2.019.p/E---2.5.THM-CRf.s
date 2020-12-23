%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:36 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 207 expanded)
%              Number of clauses        :   38 (  98 expanded)
%              Number of leaves         :   14 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  169 ( 552 expanded)
%              Number of equality atoms :   57 ( 213 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(t95_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

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

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(c_0_14,plain,(
    ! [X21,X22] :
      ( ( k2_zfmisc_1(X21,X22) != k1_xboole_0
        | X21 = k1_xboole_0
        | X22 = k1_xboole_0 )
      & ( X21 != k1_xboole_0
        | k2_zfmisc_1(X21,X22) = k1_xboole_0 )
      & ( X22 != k1_xboole_0
        | k2_zfmisc_1(X21,X22) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_15,plain,(
    ! [X25,X26] : k1_setfam_1(k2_tarski(X25,X26)) = k3_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_16,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X23,X24] : ~ r2_hidden(X23,k2_zfmisc_1(X23,X24)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_18,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X13,X14,X16,X17,X18] :
      ( ( r1_xboole_0(X13,X14)
        | r2_hidden(esk2_2(X13,X14),k3_xboole_0(X13,X14)) )
      & ( ~ r2_hidden(X18,k3_xboole_0(X16,X17))
        | ~ r1_xboole_0(X16,X17) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X44,X45] :
      ( ~ v1_relat_1(X45)
      | k1_relat_1(k7_relat_1(X45,X44)) = k3_xboole_0(k1_relat_1(X45),X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k7_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t95_relat_1])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X27,X28,X29,X31,X32,X33,X34,X36] :
      ( ( ~ r2_hidden(X29,X28)
        | r2_hidden(k4_tarski(X29,esk3_3(X27,X28,X29)),X27)
        | X28 != k1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(X31,X32),X27)
        | r2_hidden(X31,X28)
        | X28 != k1_relat_1(X27) )
      & ( ~ r2_hidden(esk4_2(X33,X34),X34)
        | ~ r2_hidden(k4_tarski(esk4_2(X33,X34),X36),X33)
        | X34 = k1_relat_1(X33) )
      & ( r2_hidden(esk4_2(X33,X34),X34)
        | r2_hidden(k4_tarski(esk4_2(X33,X34),esk5_2(X33,X34)),X33)
        | X34 = k1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_29,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_xboole_0(X7,X8) )
      & ( r2_hidden(esk1_2(X7,X8),X8)
        | r1_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_30,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & ( k7_relat_1(esk7_0,esk6_0) != k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(esk7_0),esk6_0) )
    & ( k7_relat_1(esk7_0,esk6_0) = k1_xboole_0
      | r1_xboole_0(k1_relat_1(esk7_0),esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_35,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

fof(c_0_41,plain,(
    ! [X5,X6] :
      ( ~ r1_xboole_0(X5,X6)
      | r1_xboole_0(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k7_relat_1(esk7_0,esk6_0) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(esk7_0),k1_relat_1(esk7_0),X1)) = k1_relat_1(k7_relat_1(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(esk4_2(k1_xboole_0,X1),X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( k7_relat_1(esk7_0,esk6_0) = k1_xboole_0
    | r1_xboole_0(X1,k1_relat_1(k7_relat_1(esk7_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

fof(c_0_48,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X38)
      | v1_relat_1(k7_relat_1(X38,X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_49,plain,(
    ! [X40] :
      ( ( k1_relat_1(X40) != k1_xboole_0
        | X40 = k1_xboole_0
        | ~ v1_relat_1(X40) )
      & ( k2_relat_1(X40) != k1_xboole_0
        | X40 = k1_xboole_0
        | ~ v1_relat_1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( k7_relat_1(esk7_0,esk6_0) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(k7_relat_1(esk7_0,esk6_0)),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_53,plain,(
    ! [X41,X42,X43] :
      ( ( r2_hidden(X41,X42)
        | ~ r2_hidden(X41,k1_relat_1(k7_relat_1(X43,X42)))
        | ~ v1_relat_1(X43) )
      & ( r2_hidden(X41,k1_relat_1(X43))
        | ~ r2_hidden(X41,k1_relat_1(k7_relat_1(X43,X42)))
        | ~ v1_relat_1(X43) )
      & ( ~ r2_hidden(X41,X42)
        | ~ r2_hidden(X41,k1_relat_1(X43))
        | r2_hidden(X41,k1_relat_1(k7_relat_1(X43,X42)))
        | ~ v1_relat_1(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk7_0,esk6_0)) = k1_xboole_0
    | k7_relat_1(esk7_0,esk6_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_38])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( k7_relat_1(esk7_0,esk6_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_hidden(X1,k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_34]),c_0_38])]),c_0_32])).

cnf(c_0_60,negated_conjecture,
    ( r1_xboole_0(X1,k1_relat_1(esk7_0))
    | ~ r2_hidden(esk1_2(X1,k1_relat_1(esk7_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_36])).

cnf(c_0_61,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_62,negated_conjecture,
    ( k7_relat_1(esk7_0,esk6_0) != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_63,negated_conjecture,
    ( r1_xboole_0(esk6_0,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_58])])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_63]),c_0_64]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:23:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.19/0.37  # and selection function PSelectComplexPreferEQ.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.37  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.37  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.19/0.37  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.37  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 0.19/0.37  fof(t95_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 0.19/0.37  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.19/0.37  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.37  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.19/0.37  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.37  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.19/0.37  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.19/0.37  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 0.19/0.37  fof(c_0_14, plain, ![X21, X22]:((k2_zfmisc_1(X21,X22)!=k1_xboole_0|(X21=k1_xboole_0|X22=k1_xboole_0))&((X21!=k1_xboole_0|k2_zfmisc_1(X21,X22)=k1_xboole_0)&(X22!=k1_xboole_0|k2_zfmisc_1(X21,X22)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.37  fof(c_0_15, plain, ![X25, X26]:k1_setfam_1(k2_tarski(X25,X26))=k3_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.37  fof(c_0_16, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.37  fof(c_0_17, plain, ![X23, X24]:~r2_hidden(X23,k2_zfmisc_1(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.19/0.37  cnf(c_0_18, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  fof(c_0_19, plain, ![X13, X14, X16, X17, X18]:((r1_xboole_0(X13,X14)|r2_hidden(esk2_2(X13,X14),k3_xboole_0(X13,X14)))&(~r2_hidden(X18,k3_xboole_0(X16,X17))|~r1_xboole_0(X16,X17))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.37  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  fof(c_0_22, plain, ![X44, X45]:(~v1_relat_1(X45)|k1_relat_1(k7_relat_1(X45,X44))=k3_xboole_0(k1_relat_1(X45),X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.19/0.37  fof(c_0_23, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t95_relat_1])).
% 0.19/0.37  cnf(c_0_24, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.37  cnf(c_0_25, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_18])).
% 0.19/0.37  fof(c_0_26, plain, ![X27, X28, X29, X31, X32, X33, X34, X36]:(((~r2_hidden(X29,X28)|r2_hidden(k4_tarski(X29,esk3_3(X27,X28,X29)),X27)|X28!=k1_relat_1(X27))&(~r2_hidden(k4_tarski(X31,X32),X27)|r2_hidden(X31,X28)|X28!=k1_relat_1(X27)))&((~r2_hidden(esk4_2(X33,X34),X34)|~r2_hidden(k4_tarski(esk4_2(X33,X34),X36),X33)|X34=k1_relat_1(X33))&(r2_hidden(esk4_2(X33,X34),X34)|r2_hidden(k4_tarski(esk4_2(X33,X34),esk5_2(X33,X34)),X33)|X34=k1_relat_1(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.19/0.37  cnf(c_0_27, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_28, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.37  fof(c_0_29, plain, ![X7, X8, X10, X11, X12]:(((r2_hidden(esk1_2(X7,X8),X7)|r1_xboole_0(X7,X8))&(r2_hidden(esk1_2(X7,X8),X8)|r1_xboole_0(X7,X8)))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|~r1_xboole_0(X10,X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.37  cnf(c_0_30, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  fof(c_0_31, negated_conjecture, (v1_relat_1(esk7_0)&((k7_relat_1(esk7_0,esk6_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk7_0),esk6_0))&(k7_relat_1(esk7_0,esk6_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk7_0),esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.19/0.37  cnf(c_0_32, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.37  cnf(c_0_33, plain, (r2_hidden(esk4_2(X1,X2),X2)|r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)|X2=k1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.37  cnf(c_0_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.19/0.37  cnf(c_0_35, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.37  cnf(c_0_36, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.37  cnf(c_0_37, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_30, c_0_28])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.37  cnf(c_0_39, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.37  cnf(c_0_40, plain, (X1=k1_xboole_0|r2_hidden(esk4_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.19/0.37  fof(c_0_41, plain, ![X5, X6]:(~r1_xboole_0(X5,X6)|r1_xboole_0(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.37  cnf(c_0_42, plain, (r1_xboole_0(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.37  cnf(c_0_43, negated_conjecture, (k7_relat_1(esk7_0,esk6_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk7_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.37  cnf(c_0_44, negated_conjecture, (k1_setfam_1(k1_enumset1(k1_relat_1(esk7_0),k1_relat_1(esk7_0),X1))=k1_relat_1(k7_relat_1(esk7_0,X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.37  cnf(c_0_45, plain, (X1=k1_xboole_0|~r2_hidden(esk4_2(k1_xboole_0,X1),X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.37  cnf(c_0_46, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.37  cnf(c_0_47, negated_conjecture, (k7_relat_1(esk7_0,esk6_0)=k1_xboole_0|r1_xboole_0(X1,k1_relat_1(k7_relat_1(esk7_0,esk6_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.19/0.37  fof(c_0_48, plain, ![X38, X39]:(~v1_relat_1(X38)|v1_relat_1(k7_relat_1(X38,X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.19/0.37  fof(c_0_49, plain, ![X40]:((k1_relat_1(X40)!=k1_xboole_0|X40=k1_xboole_0|~v1_relat_1(X40))&(k2_relat_1(X40)!=k1_xboole_0|X40=k1_xboole_0|~v1_relat_1(X40))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.19/0.37  cnf(c_0_50, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_45, c_0_40])).
% 0.19/0.37  cnf(c_0_51, negated_conjecture, (k7_relat_1(esk7_0,esk6_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(k7_relat_1(esk7_0,esk6_0)),X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.37  cnf(c_0_52, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.37  fof(c_0_53, plain, ![X41, X42, X43]:(((r2_hidden(X41,X42)|~r2_hidden(X41,k1_relat_1(k7_relat_1(X43,X42)))|~v1_relat_1(X43))&(r2_hidden(X41,k1_relat_1(X43))|~r2_hidden(X41,k1_relat_1(k7_relat_1(X43,X42)))|~v1_relat_1(X43)))&(~r2_hidden(X41,X42)|~r2_hidden(X41,k1_relat_1(X43))|r2_hidden(X41,k1_relat_1(k7_relat_1(X43,X42)))|~v1_relat_1(X43))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 0.19/0.37  cnf(c_0_54, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.37  cnf(c_0_55, negated_conjecture, (k1_relat_1(k7_relat_1(esk7_0,esk6_0))=k1_xboole_0|k7_relat_1(esk7_0,esk6_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.37  cnf(c_0_56, negated_conjecture, (v1_relat_1(k7_relat_1(esk7_0,X1))), inference(spm,[status(thm)],[c_0_52, c_0_38])).
% 0.19/0.37  cnf(c_0_57, plain, (r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(X3))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.37  cnf(c_0_58, negated_conjecture, (k7_relat_1(esk7_0,esk6_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 0.19/0.37  cnf(c_0_59, negated_conjecture, (~r2_hidden(X1,k1_relat_1(esk7_0))|~r2_hidden(X1,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_34]), c_0_38])]), c_0_32])).
% 0.19/0.37  cnf(c_0_60, negated_conjecture, (r1_xboole_0(X1,k1_relat_1(esk7_0))|~r2_hidden(esk1_2(X1,k1_relat_1(esk7_0)),esk6_0)), inference(spm,[status(thm)],[c_0_59, c_0_36])).
% 0.19/0.37  cnf(c_0_61, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.37  cnf(c_0_62, negated_conjecture, (k7_relat_1(esk7_0,esk6_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk7_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.37  cnf(c_0_63, negated_conjecture, (r1_xboole_0(esk6_0,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.37  cnf(c_0_64, negated_conjecture, (~r1_xboole_0(k1_relat_1(esk7_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_58])])).
% 0.19/0.37  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_63]), c_0_64]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 66
% 0.19/0.37  # Proof object clause steps            : 38
% 0.19/0.37  # Proof object formula steps           : 28
% 0.19/0.37  # Proof object conjectures             : 17
% 0.19/0.37  # Proof object clause conjectures      : 14
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 18
% 0.19/0.37  # Proof object initial formulas used   : 14
% 0.19/0.37  # Proof object generating inferences   : 15
% 0.19/0.37  # Proof object simplifying inferences  : 15
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 14
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 28
% 0.19/0.37  # Removed in clause preprocessing      : 2
% 0.19/0.37  # Initial clauses in saturation        : 26
% 0.19/0.37  # Processed clauses                    : 164
% 0.19/0.37  # ...of these trivial                  : 10
% 0.19/0.37  # ...subsumed                          : 35
% 0.19/0.37  # ...remaining for further processing  : 119
% 0.19/0.37  # Other redundant clauses eliminated   : 6
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 25
% 0.19/0.37  # Generated clauses                    : 368
% 0.19/0.37  # ...of the previous two non-trivial   : 250
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 354
% 0.19/0.37  # Factorizations                       : 8
% 0.19/0.37  # Equation resolutions                 : 6
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 64
% 0.19/0.37  #    Positive orientable unit clauses  : 21
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 3
% 0.19/0.37  #    Non-unit-clauses                  : 40
% 0.19/0.37  # Current number of unprocessed clauses: 106
% 0.19/0.37  # ...number of literals in the above   : 223
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 53
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 333
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 291
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 17
% 0.19/0.37  # Unit Clause-clause subsumption calls : 29
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 31
% 0.19/0.37  # BW rewrite match successes           : 13
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 6399
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.034 s
% 0.19/0.37  # System time              : 0.005 s
% 0.19/0.37  # Total time               : 0.039 s
% 0.19/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
