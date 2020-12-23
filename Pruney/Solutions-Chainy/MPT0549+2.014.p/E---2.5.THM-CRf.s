%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:45 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 324 expanded)
%              Number of clauses        :   52 ( 143 expanded)
%              Number of leaves         :   14 (  84 expanded)
%              Depth                    :   20
%              Number of atoms          :  184 ( 918 expanded)
%              Number of equality atoms :   56 ( 289 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

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

fof(t151_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k9_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(c_0_14,plain,(
    ! [X30,X31,X32] :
      ( ( r2_hidden(X30,X31)
        | ~ r2_hidden(X30,k1_relat_1(k7_relat_1(X32,X31)))
        | ~ v1_relat_1(X32) )
      & ( r2_hidden(X30,k1_relat_1(X32))
        | ~ r2_hidden(X30,k1_relat_1(k7_relat_1(X32,X31)))
        | ~ v1_relat_1(X32) )
      & ( ~ r2_hidden(X30,X31)
        | ~ r2_hidden(X30,k1_relat_1(X32))
        | r2_hidden(X30,k1_relat_1(k7_relat_1(X32,X31)))
        | ~ v1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

fof(c_0_15,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_xboole_0(X7,X8) )
      & ( r2_hidden(esk1_2(X7,X8),X8)
        | r1_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k9_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t151_relat_1])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & ( k9_relat_1(esk4_0,esk3_0) != k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(esk4_0),esk3_0) )
    & ( k9_relat_1(esk4_0,esk3_0) = k1_xboole_0
      | r1_xboole_0(k1_relat_1(esk4_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(X2,X3))),X3)
    | r1_xboole_0(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(esk4_0,X2))),X2)
    | r1_xboole_0(X1,k1_relat_1(k7_relat_1(esk4_0,X2))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(X2,X3))),k1_relat_1(X2))
    | r1_xboole_0(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( r1_xboole_0(X1,k1_relat_1(k7_relat_1(esk4_0,X2)))
    | ~ r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(esk4_0,X2))),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(esk4_0,X2))),k1_relat_1(esk4_0))
    | r1_xboole_0(X1,k1_relat_1(k7_relat_1(esk4_0,X2))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_21])).

fof(c_0_28,plain,(
    ! [X13] :
      ( ( r1_xboole_0(X13,X13)
        | X13 != k1_xboole_0 )
      & ( X13 = k1_xboole_0
        | ~ r1_xboole_0(X13,X13) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

cnf(c_0_29,negated_conjecture,
    ( r1_xboole_0(X1,k1_relat_1(k7_relat_1(esk4_0,X2)))
    | ~ r1_xboole_0(k1_relat_1(esk4_0),X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( k9_relat_1(esk4_0,esk3_0) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_31,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | k2_relat_1(k7_relat_1(X27,X26)) = k9_relat_1(X27,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_32,plain,(
    ! [X14,X15] :
      ( ( k2_zfmisc_1(X14,X15) != k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0 )
      & ( X14 != k1_xboole_0
        | k2_zfmisc_1(X14,X15) = k1_xboole_0 )
      & ( X15 != k1_xboole_0
        | k2_zfmisc_1(X14,X15) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_33,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | v1_relat_1(k7_relat_1(X19,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_34,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X34)
      | ~ r1_tarski(k1_relat_1(X34),X33)
      | k7_relat_1(X34,X33) = X34 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

fof(c_0_35,plain,(
    ! [X29] :
      ( k1_relat_1(k6_relat_1(X29)) = X29
      & k2_relat_1(k6_relat_1(X29)) = X29 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_36,plain,(
    ! [X18] : v1_relat_1(k6_relat_1(X18)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_37,plain,(
    ! [X28] :
      ( ~ v1_relat_1(X28)
      | r1_tarski(X28,k2_zfmisc_1(k1_relat_1(X28),k2_relat_1(X28))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( k9_relat_1(esk4_0,esk3_0) = k1_xboole_0
    | r1_xboole_0(X1,k1_relat_1(k7_relat_1(esk4_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,esk3_0)) = k1_xboole_0
    | k9_relat_1(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk4_0,X1)) = k9_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_21])).

cnf(c_0_49,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_21])).

fof(c_0_51,plain,(
    ! [X16,X17] : ~ r2_hidden(X16,k2_zfmisc_1(X16,X17)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_52,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_53,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_54,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_55,negated_conjecture,
    ( k9_relat_1(esk4_0,esk3_0) = k1_xboole_0
    | r1_tarski(k7_relat_1(esk4_0,esk3_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49]),c_0_50])])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_58,plain,
    ( r2_hidden(esk1_2(k1_relat_1(k7_relat_1(X1,X2)),X3),X2)
    | r1_xboole_0(k1_relat_1(k7_relat_1(X1,X2)),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( k7_relat_1(k6_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_xboole_0) = k6_relat_1(k7_relat_1(esk4_0,esk3_0))
    | k9_relat_1(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( k9_relat_1(esk4_0,esk3_0) = k1_xboole_0
    | r1_xboole_0(k7_relat_1(esk4_0,esk3_0),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_44]),c_0_44]),c_0_45])]),c_0_60])).

cnf(c_0_62,negated_conjecture,
    ( k9_relat_1(esk4_0,esk3_0) = k1_xboole_0
    | k7_relat_1(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_61])).

cnf(c_0_63,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk4_0,X1),k2_zfmisc_1(k1_relat_1(k7_relat_1(esk4_0,X1)),k9_relat_1(esk4_0,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_50]),c_0_48])).

cnf(c_0_65,negated_conjecture,
    ( k9_relat_1(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_62]),c_0_63]),c_0_21])])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk4_0,esk3_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( k7_relat_1(k6_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_xboole_0) = k6_relat_1(k7_relat_1(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_66])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(k7_relat_1(esk4_0,esk3_0),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_67]),c_0_44]),c_0_44]),c_0_45])]),c_0_60])).

cnf(c_0_70,plain,
    ( r2_hidden(esk1_2(X1,k1_relat_1(X2)),k1_relat_1(k7_relat_1(X2,X3)))
    | r1_xboole_0(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk1_2(X1,k1_relat_1(X2)),X3) ),
    inference(spm,[status(thm)],[c_0_68,c_0_18])).

cnf(c_0_71,negated_conjecture,
    ( k7_relat_1(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_69])).

cnf(c_0_72,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

fof(c_0_73,plain,(
    ! [X5,X6] :
      ( ~ r1_xboole_0(X5,X6)
      | r1_xboole_0(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_74,negated_conjecture,
    ( r1_xboole_0(X1,k1_relat_1(esk4_0))
    | ~ r2_hidden(esk1_2(X1,k1_relat_1(esk4_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_21])]),c_0_60])).

cnf(c_0_75,negated_conjecture,
    ( k9_relat_1(esk4_0,esk3_0) != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_76,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(esk3_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_53])).

cnf(c_0_78,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_65])])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:01:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.20/0.40  # and selection function PSelectComplexPreferEQ.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.027 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 0.20/0.40  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.40  fof(t151_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 0.20/0.40  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.20/0.40  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.20/0.40  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.40  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.20/0.40  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.20/0.40  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.20/0.40  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.20/0.40  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 0.20/0.40  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.20/0.40  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.20/0.40  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.40  fof(c_0_14, plain, ![X30, X31, X32]:(((r2_hidden(X30,X31)|~r2_hidden(X30,k1_relat_1(k7_relat_1(X32,X31)))|~v1_relat_1(X32))&(r2_hidden(X30,k1_relat_1(X32))|~r2_hidden(X30,k1_relat_1(k7_relat_1(X32,X31)))|~v1_relat_1(X32)))&(~r2_hidden(X30,X31)|~r2_hidden(X30,k1_relat_1(X32))|r2_hidden(X30,k1_relat_1(k7_relat_1(X32,X31)))|~v1_relat_1(X32))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 0.20/0.40  fof(c_0_15, plain, ![X7, X8, X10, X11, X12]:(((r2_hidden(esk1_2(X7,X8),X7)|r1_xboole_0(X7,X8))&(r2_hidden(esk1_2(X7,X8),X8)|r1_xboole_0(X7,X8)))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|~r1_xboole_0(X10,X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.40  fof(c_0_16, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t151_relat_1])).
% 0.20/0.40  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_18, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  fof(c_0_19, negated_conjecture, (v1_relat_1(esk4_0)&((k9_relat_1(esk4_0,esk3_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk4_0),esk3_0))&(k9_relat_1(esk4_0,esk3_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk4_0),esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.20/0.40  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(X2,X3))),X3)|r1_xboole_0(X1,k1_relat_1(k7_relat_1(X2,X3)))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.40  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_22, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3)))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_23, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_24, negated_conjecture, (r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(esk4_0,X2))),X2)|r1_xboole_0(X1,k1_relat_1(k7_relat_1(esk4_0,X2)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.40  cnf(c_0_25, plain, (r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(X2,X3))),k1_relat_1(X2))|r1_xboole_0(X1,k1_relat_1(k7_relat_1(X2,X3)))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_22, c_0_18])).
% 0.20/0.40  cnf(c_0_26, negated_conjecture, (r1_xboole_0(X1,k1_relat_1(k7_relat_1(esk4_0,X2)))|~r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(esk4_0,X2))),X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.40  cnf(c_0_27, negated_conjecture, (r2_hidden(esk1_2(X1,k1_relat_1(k7_relat_1(esk4_0,X2))),k1_relat_1(esk4_0))|r1_xboole_0(X1,k1_relat_1(k7_relat_1(esk4_0,X2)))), inference(spm,[status(thm)],[c_0_25, c_0_21])).
% 0.20/0.40  fof(c_0_28, plain, ![X13]:((r1_xboole_0(X13,X13)|X13!=k1_xboole_0)&(X13=k1_xboole_0|~r1_xboole_0(X13,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.20/0.40  cnf(c_0_29, negated_conjecture, (r1_xboole_0(X1,k1_relat_1(k7_relat_1(esk4_0,X2)))|~r1_xboole_0(k1_relat_1(esk4_0),X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.40  cnf(c_0_30, negated_conjecture, (k9_relat_1(esk4_0,esk3_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  fof(c_0_31, plain, ![X26, X27]:(~v1_relat_1(X27)|k2_relat_1(k7_relat_1(X27,X26))=k9_relat_1(X27,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.20/0.40  fof(c_0_32, plain, ![X14, X15]:((k2_zfmisc_1(X14,X15)!=k1_xboole_0|(X14=k1_xboole_0|X15=k1_xboole_0))&((X14!=k1_xboole_0|k2_zfmisc_1(X14,X15)=k1_xboole_0)&(X15!=k1_xboole_0|k2_zfmisc_1(X14,X15)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.40  fof(c_0_33, plain, ![X19, X20]:(~v1_relat_1(X19)|v1_relat_1(k7_relat_1(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.20/0.40  fof(c_0_34, plain, ![X33, X34]:(~v1_relat_1(X34)|(~r1_tarski(k1_relat_1(X34),X33)|k7_relat_1(X34,X33)=X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.20/0.40  fof(c_0_35, plain, ![X29]:(k1_relat_1(k6_relat_1(X29))=X29&k2_relat_1(k6_relat_1(X29))=X29), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.20/0.40  fof(c_0_36, plain, ![X18]:v1_relat_1(k6_relat_1(X18)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.20/0.40  fof(c_0_37, plain, ![X28]:(~v1_relat_1(X28)|r1_tarski(X28,k2_zfmisc_1(k1_relat_1(X28),k2_relat_1(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.20/0.40  cnf(c_0_38, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.40  cnf(c_0_39, negated_conjecture, (k9_relat_1(esk4_0,esk3_0)=k1_xboole_0|r1_xboole_0(X1,k1_relat_1(k7_relat_1(esk4_0,esk3_0)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.40  cnf(c_0_40, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.40  cnf(c_0_41, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.40  cnf(c_0_42, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.40  cnf(c_0_43, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.40  cnf(c_0_44, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.40  cnf(c_0_45, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.40  cnf(c_0_46, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,esk3_0))=k1_xboole_0|k9_relat_1(esk4_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.40  cnf(c_0_48, negated_conjecture, (k2_relat_1(k7_relat_1(esk4_0,X1))=k9_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_21])).
% 0.20/0.40  cnf(c_0_49, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_41])).
% 0.20/0.40  cnf(c_0_50, negated_conjecture, (v1_relat_1(k7_relat_1(esk4_0,X1))), inference(spm,[status(thm)],[c_0_42, c_0_21])).
% 0.20/0.40  fof(c_0_51, plain, ![X16, X17]:~r2_hidden(X16,k2_zfmisc_1(X16,X17)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.20/0.40  cnf(c_0_52, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.40  cnf(c_0_53, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_54, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.20/0.40  cnf(c_0_55, negated_conjecture, (k9_relat_1(esk4_0,esk3_0)=k1_xboole_0|r1_tarski(k7_relat_1(esk4_0,esk3_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49]), c_0_50])])).
% 0.20/0.40  cnf(c_0_56, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.40  cnf(c_0_57, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_52])).
% 0.20/0.40  cnf(c_0_58, plain, (r2_hidden(esk1_2(k1_relat_1(k7_relat_1(X1,X2)),X3),X2)|r1_xboole_0(k1_relat_1(k7_relat_1(X1,X2)),X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_53])).
% 0.20/0.40  cnf(c_0_59, negated_conjecture, (k7_relat_1(k6_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_xboole_0)=k6_relat_1(k7_relat_1(esk4_0,esk3_0))|k9_relat_1(esk4_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.40  cnf(c_0_60, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.40  cnf(c_0_61, negated_conjecture, (k9_relat_1(esk4_0,esk3_0)=k1_xboole_0|r1_xboole_0(k7_relat_1(esk4_0,esk3_0),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_44]), c_0_44]), c_0_45])]), c_0_60])).
% 0.20/0.40  cnf(c_0_62, negated_conjecture, (k9_relat_1(esk4_0,esk3_0)=k1_xboole_0|k7_relat_1(esk4_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_61])).
% 0.20/0.40  cnf(c_0_63, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.40  cnf(c_0_64, negated_conjecture, (r1_tarski(k7_relat_1(esk4_0,X1),k2_zfmisc_1(k1_relat_1(k7_relat_1(esk4_0,X1)),k9_relat_1(esk4_0,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_50]), c_0_48])).
% 0.20/0.40  cnf(c_0_65, negated_conjecture, (k9_relat_1(esk4_0,esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_62]), c_0_63]), c_0_21])])).
% 0.20/0.40  cnf(c_0_66, negated_conjecture, (r1_tarski(k7_relat_1(esk4_0,esk3_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_57])).
% 0.20/0.40  cnf(c_0_67, negated_conjecture, (k7_relat_1(k6_relat_1(k7_relat_1(esk4_0,esk3_0)),k1_xboole_0)=k6_relat_1(k7_relat_1(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_54, c_0_66])).
% 0.20/0.40  cnf(c_0_68, plain, (r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(X3))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_69, negated_conjecture, (r1_xboole_0(k7_relat_1(esk4_0,esk3_0),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_67]), c_0_44]), c_0_44]), c_0_45])]), c_0_60])).
% 0.20/0.40  cnf(c_0_70, plain, (r2_hidden(esk1_2(X1,k1_relat_1(X2)),k1_relat_1(k7_relat_1(X2,X3)))|r1_xboole_0(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(esk1_2(X1,k1_relat_1(X2)),X3)), inference(spm,[status(thm)],[c_0_68, c_0_18])).
% 0.20/0.40  cnf(c_0_71, negated_conjecture, (k7_relat_1(esk4_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_69])).
% 0.20/0.40  cnf(c_0_72, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.40  fof(c_0_73, plain, ![X5, X6]:(~r1_xboole_0(X5,X6)|r1_xboole_0(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.40  cnf(c_0_74, negated_conjecture, (r1_xboole_0(X1,k1_relat_1(esk4_0))|~r2_hidden(esk1_2(X1,k1_relat_1(esk4_0)),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), c_0_21])]), c_0_60])).
% 0.20/0.40  cnf(c_0_75, negated_conjecture, (k9_relat_1(esk4_0,esk3_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_76, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.20/0.40  cnf(c_0_77, negated_conjecture, (r1_xboole_0(esk3_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_74, c_0_53])).
% 0.20/0.40  cnf(c_0_78, negated_conjecture, (~r1_xboole_0(k1_relat_1(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_65])])).
% 0.20/0.40  cnf(c_0_79, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 80
% 0.20/0.40  # Proof object clause steps            : 52
% 0.20/0.40  # Proof object formula steps           : 28
% 0.20/0.40  # Proof object conjectures             : 28
% 0.20/0.40  # Proof object clause conjectures      : 25
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 22
% 0.20/0.40  # Proof object initial formulas used   : 14
% 0.20/0.40  # Proof object generating inferences   : 27
% 0.20/0.40  # Proof object simplifying inferences  : 30
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 15
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 29
% 0.20/0.40  # Removed in clause preprocessing      : 0
% 0.20/0.40  # Initial clauses in saturation        : 29
% 0.20/0.40  # Processed clauses                    : 498
% 0.20/0.40  # ...of these trivial                  : 17
% 0.20/0.40  # ...subsumed                          : 195
% 0.20/0.40  # ...remaining for further processing  : 286
% 0.20/0.40  # Other redundant clauses eliminated   : 5
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 36
% 0.20/0.40  # Backward-rewritten                   : 87
% 0.20/0.40  # Generated clauses                    : 1605
% 0.20/0.40  # ...of the previous two non-trivial   : 1091
% 0.20/0.40  # Contextual simplify-reflections      : 0
% 0.20/0.40  # Paramodulations                      : 1592
% 0.20/0.40  # Factorizations                       : 8
% 0.20/0.40  # Equation resolutions                 : 5
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 131
% 0.20/0.40  #    Positive orientable unit clauses  : 48
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 3
% 0.20/0.40  #    Non-unit-clauses                  : 80
% 0.20/0.40  # Current number of unprocessed clauses: 508
% 0.20/0.40  # ...number of literals in the above   : 1081
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 152
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 2803
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 2577
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 161
% 0.20/0.40  # Unit Clause-clause subsumption calls : 130
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 64
% 0.20/0.40  # BW rewrite match successes           : 17
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 26317
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.057 s
% 0.20/0.40  # System time              : 0.007 s
% 0.20/0.40  # Total time               : 0.064 s
% 0.20/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
