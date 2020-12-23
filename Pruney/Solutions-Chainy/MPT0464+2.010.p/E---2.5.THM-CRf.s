%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:38 EST 2020

% Result     : Theorem 0.90s
% Output     : CNFRefutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 459 expanded)
%              Number of clauses        :   55 ( 201 expanded)
%              Number of leaves         :   14 ( 120 expanded)
%              Depth                    :   15
%              Number of atoms          :  270 (1307 expanded)
%              Number of equality atoms :  127 ( 616 expanded)
%              Maximal formula depth    :   32 (   4 average)
%              Maximal clause size      :   44 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t52_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t50_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ! [X4] :
                  ( v1_relat_1(X4)
                 => ( ( r1_tarski(X1,X2)
                      & r1_tarski(X3,X4) )
                   => r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(d3_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( X6 = k3_enumset1(X1,X2,X3,X4,X5)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X7 != X1
              & X7 != X2
              & X7 != X3
              & X7 != X4
              & X7 != X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(c_0_14,plain,(
    ! [X44,X45] : k1_setfam_1(k2_tarski(X44,X45)) = k3_xboole_0(X44,X45) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_15,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relat_1])).

fof(c_0_17,plain,(
    ! [X10,X11] : r1_tarski(k3_xboole_0(X10,X11),X10) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_21,plain,(
    ! [X20,X21,X22,X23] : k3_enumset1(X20,X20,X21,X22,X23) = k2_enumset1(X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_22,plain,(
    ! [X24,X25,X26,X27,X28] : k4_enumset1(X24,X24,X25,X26,X27,X28) = k3_enumset1(X24,X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_23,plain,(
    ! [X52,X53,X54,X55] :
      ( ~ v1_relat_1(X52)
      | ~ v1_relat_1(X53)
      | ~ v1_relat_1(X54)
      | ~ v1_relat_1(X55)
      | ~ r1_tarski(X52,X53)
      | ~ r1_tarski(X54,X55)
      | r1_tarski(k5_relat_1(X52,X54),k5_relat_1(X53,X55)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_relat_1])])])).

fof(c_0_24,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & ~ r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_25,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_26,plain,(
    ! [X46,X47] :
      ( ( ~ m1_subset_1(X46,k1_zfmisc_1(X47))
        | r1_tarski(X46,X47) )
      & ( ~ r1_tarski(X46,X47)
        | m1_subset_1(X46,k1_zfmisc_1(X47)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_27,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_35,plain,(
    ! [X50,X51] :
      ( ~ v1_relat_1(X50)
      | ~ m1_subset_1(X51,k1_zfmisc_1(X50))
      | v1_relat_1(X51) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31])).

fof(c_0_38,plain,(
    ! [X29,X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40,X41,X42] :
      ( ( ~ r2_hidden(X35,X34)
        | X35 = X29
        | X35 = X30
        | X35 = X31
        | X35 = X32
        | X35 = X33
        | X34 != k3_enumset1(X29,X30,X31,X32,X33) )
      & ( X36 != X29
        | r2_hidden(X36,X34)
        | X34 != k3_enumset1(X29,X30,X31,X32,X33) )
      & ( X36 != X30
        | r2_hidden(X36,X34)
        | X34 != k3_enumset1(X29,X30,X31,X32,X33) )
      & ( X36 != X31
        | r2_hidden(X36,X34)
        | X34 != k3_enumset1(X29,X30,X31,X32,X33) )
      & ( X36 != X32
        | r2_hidden(X36,X34)
        | X34 != k3_enumset1(X29,X30,X31,X32,X33) )
      & ( X36 != X33
        | r2_hidden(X36,X34)
        | X34 != k3_enumset1(X29,X30,X31,X32,X33) )
      & ( esk1_6(X37,X38,X39,X40,X41,X42) != X37
        | ~ r2_hidden(esk1_6(X37,X38,X39,X40,X41,X42),X42)
        | X42 = k3_enumset1(X37,X38,X39,X40,X41) )
      & ( esk1_6(X37,X38,X39,X40,X41,X42) != X38
        | ~ r2_hidden(esk1_6(X37,X38,X39,X40,X41,X42),X42)
        | X42 = k3_enumset1(X37,X38,X39,X40,X41) )
      & ( esk1_6(X37,X38,X39,X40,X41,X42) != X39
        | ~ r2_hidden(esk1_6(X37,X38,X39,X40,X41,X42),X42)
        | X42 = k3_enumset1(X37,X38,X39,X40,X41) )
      & ( esk1_6(X37,X38,X39,X40,X41,X42) != X40
        | ~ r2_hidden(esk1_6(X37,X38,X39,X40,X41,X42),X42)
        | X42 = k3_enumset1(X37,X38,X39,X40,X41) )
      & ( esk1_6(X37,X38,X39,X40,X41,X42) != X41
        | ~ r2_hidden(esk1_6(X37,X38,X39,X40,X41,X42),X42)
        | X42 = k3_enumset1(X37,X38,X39,X40,X41) )
      & ( r2_hidden(esk1_6(X37,X38,X39,X40,X41,X42),X42)
        | esk1_6(X37,X38,X39,X40,X41,X42) = X37
        | esk1_6(X37,X38,X39,X40,X41,X42) = X38
        | esk1_6(X37,X38,X39,X40,X41,X42) = X39
        | esk1_6(X37,X38,X39,X40,X41,X42) = X40
        | esk1_6(X37,X38,X39,X40,X41,X42) = X41
        | X42 = k3_enumset1(X37,X38,X39,X40,X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(esk2_0,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( m1_subset_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X5,X6,X7,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_33]),c_0_40])])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_46,plain,
    ( v1_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_48,plain,(
    ! [X48,X49] :
      ( ~ r2_hidden(X48,X49)
      | r1_tarski(k1_setfam_1(X49),X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X4,X4,X5,X6,X7,X2) ),
    inference(rw,[status(thm)],[c_0_43,c_0_31])).

cnf(c_0_50,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | X1 = X7
    | ~ r2_hidden(X1,X2)
    | X2 != k3_enumset1(X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_51,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_tarski(X12,X14)
      | r1_tarski(X12,k3_xboole_0(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk4_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k4_enumset1(X2,X2,X3,X4,X5,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_49])])).

cnf(c_0_56,plain,
    ( X1 = X7
    | X1 = X6
    | X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k4_enumset1(X3,X3,X4,X5,X6,X7)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_50,c_0_31])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6)
    | esk1_6(X1,X2,X3,X4,X5,X6) = X1
    | esk1_6(X1,X2,X3,X4,X5,X6) = X2
    | esk1_6(X1,X2,X3,X4,X5,X6) = X3
    | esk1_6(X1,X2,X3,X4,X5,X6) = X4
    | esk1_6(X1,X2,X3,X4,X5,X6) = X5
    | X6 = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))),k5_relat_1(esk2_0,esk4_0))
    | ~ r1_tarski(k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,X5)),X5) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_62,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | ~ r2_hidden(X1,k4_enumset1(X6,X6,X5,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_63,plain,
    ( X6 = k4_enumset1(X1,X1,X2,X3,X4,X5)
    | esk1_6(X1,X2,X3,X4,X5,X6) = X5
    | esk1_6(X1,X2,X3,X4,X5,X6) = X4
    | esk1_6(X1,X2,X3,X4,X5,X6) = X3
    | esk1_6(X1,X2,X3,X4,X5,X6) = X2
    | esk1_6(X1,X2,X3,X4,X5,X6) = X1
    | r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6) ),
    inference(rw,[status(thm)],[c_0_57,c_0_31])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_28]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k5_relat_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk3_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_47])).

cnf(c_0_67,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k4_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31])).

cnf(c_0_68,plain,
    ( esk1_6(X1,X2,X3,X4,X5,k4_enumset1(X6,X6,X7,X8,X9,X10)) = X1
    | esk1_6(X1,X2,X3,X4,X5,k4_enumset1(X6,X6,X7,X8,X9,X10)) = X2
    | esk1_6(X1,X2,X3,X4,X5,k4_enumset1(X6,X6,X7,X8,X9,X10)) = X3
    | esk1_6(X1,X2,X3,X4,X5,k4_enumset1(X6,X6,X7,X8,X9,X10)) = X4
    | esk1_6(X1,X2,X3,X4,X5,k4_enumset1(X6,X6,X7,X8,X9,X10)) = X5
    | k4_enumset1(X6,X6,X7,X8,X9,X10) = k4_enumset1(X1,X1,X2,X3,X4,X5)
    | esk1_6(X1,X2,X3,X4,X5,k4_enumset1(X6,X6,X7,X8,X9,X10)) = X10
    | esk1_6(X1,X2,X3,X4,X5,k4_enumset1(X6,X6,X7,X8,X9,X10)) = X9
    | esk1_6(X1,X2,X3,X4,X5,k4_enumset1(X6,X6,X7,X8,X9,X10)) = X8
    | esk1_6(X1,X2,X3,X4,X5,k4_enumset1(X6,X6,X7,X8,X9,X10)) = X7
    | esk1_6(X1,X2,X3,X4,X5,k4_enumset1(X6,X6,X7,X8,X9,X10)) = X6 ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k4_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),X1)))
    | ~ r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))),k5_relat_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_53]),c_0_37])])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_72,plain,
    ( X6 = k3_enumset1(X1,X2,X3,X4,X5)
    | esk1_6(X1,X2,X3,X4,X5,X6) != X5
    | ~ r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_73,negated_conjecture,
    ( esk1_6(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0),k4_enumset1(X1,X1,X2,X3,X4,X5)) = k5_relat_1(esk2_0,esk4_0)
    | esk1_6(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0),k4_enumset1(X1,X1,X2,X3,X4,X5)) = k5_relat_1(esk2_0,esk3_0)
    | esk1_6(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0),k4_enumset1(X1,X1,X2,X3,X4,X5)) = X1
    | esk1_6(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0),k4_enumset1(X1,X1,X2,X3,X4,X5)) = X2
    | esk1_6(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0),k4_enumset1(X1,X1,X2,X3,X4,X5)) = X3
    | esk1_6(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0),k4_enumset1(X1,X1,X2,X3,X4,X5)) = X4
    | esk1_6(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0),k4_enumset1(X1,X1,X2,X3,X4,X5)) = X5
    | ~ r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,X5))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k4_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X2,X2,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[c_0_71,c_0_31])).

cnf(c_0_76,plain,
    ( X6 = k3_enumset1(X1,X2,X3,X4,X5)
    | esk1_6(X1,X2,X3,X4,X5,X6) != X4
    | ~ r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_77,plain,
    ( X6 = k4_enumset1(X1,X1,X2,X3,X4,X5)
    | esk1_6(X1,X2,X3,X4,X5,X6) != X5
    | ~ r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6) ),
    inference(rw,[status(thm)],[c_0_72,c_0_31])).

cnf(c_0_78,negated_conjecture,
    ( esk1_6(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0),k4_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0))) = k5_relat_1(esk2_0,esk3_0)
    | esk1_6(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0),k4_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0))) = k5_relat_1(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,k4_enumset1(X1,X1,X2,X3,X4,X5)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_75])])).

cnf(c_0_80,plain,
    ( X6 = k4_enumset1(X1,X1,X2,X3,X4,X5)
    | esk1_6(X1,X2,X3,X4,X5,X6) != X4
    | ~ r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6) ),
    inference(rw,[status(thm)],[c_0_76,c_0_31])).

cnf(c_0_81,negated_conjecture,
    ( esk1_6(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0),k4_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0))) = k5_relat_1(esk2_0,esk3_0)
    | k4_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0)) = k4_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])])).

cnf(c_0_82,negated_conjecture,
    ( k4_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0)) = k4_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_55])])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_82]),c_0_67]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.90/1.07  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S002I
% 0.90/1.07  # and selection function SelectNegativeLiterals.
% 0.90/1.07  #
% 0.90/1.07  # Preprocessing time       : 0.027 s
% 0.90/1.07  # Presaturation interreduction done
% 0.90/1.07  
% 0.90/1.07  # Proof found!
% 0.90/1.07  # SZS status Theorem
% 0.90/1.07  # SZS output start CNFRefutation
% 0.90/1.07  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.90/1.07  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.90/1.07  fof(t52_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 0.90/1.07  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.90/1.07  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.90/1.07  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.90/1.07  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.90/1.07  fof(t50_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relat_1)).
% 0.90/1.07  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.90/1.07  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.90/1.07  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.90/1.07  fof(d3_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:(X6=k3_enumset1(X1,X2,X3,X4,X5)<=>![X7]:(r2_hidden(X7,X6)<=>~(((((X7!=X1&X7!=X2)&X7!=X3)&X7!=X4)&X7!=X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 0.90/1.07  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.90/1.07  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.90/1.07  fof(c_0_14, plain, ![X44, X45]:k1_setfam_1(k2_tarski(X44,X45))=k3_xboole_0(X44,X45), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.90/1.07  fof(c_0_15, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.90/1.07  fof(c_0_16, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t52_relat_1])).
% 0.90/1.07  fof(c_0_17, plain, ![X10, X11]:r1_tarski(k3_xboole_0(X10,X11),X10), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.90/1.07  cnf(c_0_18, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.90/1.07  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.90/1.07  fof(c_0_20, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.90/1.07  fof(c_0_21, plain, ![X20, X21, X22, X23]:k3_enumset1(X20,X20,X21,X22,X23)=k2_enumset1(X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.90/1.07  fof(c_0_22, plain, ![X24, X25, X26, X27, X28]:k4_enumset1(X24,X24,X25,X26,X27,X28)=k3_enumset1(X24,X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.90/1.07  fof(c_0_23, plain, ![X52, X53, X54, X55]:(~v1_relat_1(X52)|(~v1_relat_1(X53)|(~v1_relat_1(X54)|(~v1_relat_1(X55)|(~r1_tarski(X52,X53)|~r1_tarski(X54,X55)|r1_tarski(k5_relat_1(X52,X54),k5_relat_1(X53,X55))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_relat_1])])])).
% 0.90/1.07  fof(c_0_24, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&~r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.90/1.07  fof(c_0_25, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.90/1.07  fof(c_0_26, plain, ![X46, X47]:((~m1_subset_1(X46,k1_zfmisc_1(X47))|r1_tarski(X46,X47))&(~r1_tarski(X46,X47)|m1_subset_1(X46,k1_zfmisc_1(X47)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.90/1.07  cnf(c_0_27, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.90/1.07  cnf(c_0_28, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.90/1.07  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.90/1.07  cnf(c_0_30, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.90/1.07  cnf(c_0_31, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.90/1.07  cnf(c_0_32, plain, (r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~v1_relat_1(X4)|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.90/1.07  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.90/1.07  cnf(c_0_34, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.90/1.07  fof(c_0_35, plain, ![X50, X51]:(~v1_relat_1(X50)|(~m1_subset_1(X51,k1_zfmisc_1(X50))|v1_relat_1(X51))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.90/1.07  cnf(c_0_36, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.90/1.07  cnf(c_0_37, plain, (r1_tarski(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30]), c_0_31])).
% 0.90/1.07  fof(c_0_38, plain, ![X29, X30, X31, X32, X33, X34, X35, X36, X37, X38, X39, X40, X41, X42]:(((~r2_hidden(X35,X34)|(X35=X29|X35=X30|X35=X31|X35=X32|X35=X33)|X34!=k3_enumset1(X29,X30,X31,X32,X33))&(((((X36!=X29|r2_hidden(X36,X34)|X34!=k3_enumset1(X29,X30,X31,X32,X33))&(X36!=X30|r2_hidden(X36,X34)|X34!=k3_enumset1(X29,X30,X31,X32,X33)))&(X36!=X31|r2_hidden(X36,X34)|X34!=k3_enumset1(X29,X30,X31,X32,X33)))&(X36!=X32|r2_hidden(X36,X34)|X34!=k3_enumset1(X29,X30,X31,X32,X33)))&(X36!=X33|r2_hidden(X36,X34)|X34!=k3_enumset1(X29,X30,X31,X32,X33))))&((((((esk1_6(X37,X38,X39,X40,X41,X42)!=X37|~r2_hidden(esk1_6(X37,X38,X39,X40,X41,X42),X42)|X42=k3_enumset1(X37,X38,X39,X40,X41))&(esk1_6(X37,X38,X39,X40,X41,X42)!=X38|~r2_hidden(esk1_6(X37,X38,X39,X40,X41,X42),X42)|X42=k3_enumset1(X37,X38,X39,X40,X41)))&(esk1_6(X37,X38,X39,X40,X41,X42)!=X39|~r2_hidden(esk1_6(X37,X38,X39,X40,X41,X42),X42)|X42=k3_enumset1(X37,X38,X39,X40,X41)))&(esk1_6(X37,X38,X39,X40,X41,X42)!=X40|~r2_hidden(esk1_6(X37,X38,X39,X40,X41,X42),X42)|X42=k3_enumset1(X37,X38,X39,X40,X41)))&(esk1_6(X37,X38,X39,X40,X41,X42)!=X41|~r2_hidden(esk1_6(X37,X38,X39,X40,X41,X42),X42)|X42=k3_enumset1(X37,X38,X39,X40,X41)))&(r2_hidden(esk1_6(X37,X38,X39,X40,X41,X42),X42)|(esk1_6(X37,X38,X39,X40,X41,X42)=X37|esk1_6(X37,X38,X39,X40,X41,X42)=X38|esk1_6(X37,X38,X39,X40,X41,X42)=X39|esk1_6(X37,X38,X39,X40,X41,X42)=X40|esk1_6(X37,X38,X39,X40,X41,X42)=X41)|X42=k3_enumset1(X37,X38,X39,X40,X41)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).
% 0.90/1.07  cnf(c_0_39, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(X2,X3))|~v1_relat_1(X3)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(esk2_0,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.90/1.07  cnf(c_0_40, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_34])).
% 0.90/1.07  cnf(c_0_41, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.90/1.07  cnf(c_0_42, plain, (m1_subset_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.90/1.07  cnf(c_0_43, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X5,X6,X7,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.90/1.07  cnf(c_0_44, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_33]), c_0_40])])).
% 0.90/1.07  cnf(c_0_45, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.90/1.07  cnf(c_0_46, plain, (v1_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.90/1.07  cnf(c_0_47, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.90/1.07  fof(c_0_48, plain, ![X48, X49]:(~r2_hidden(X48,X49)|r1_tarski(k1_setfam_1(X49),X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.90/1.07  cnf(c_0_49, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X4,X4,X5,X6,X7,X2)), inference(rw,[status(thm)],[c_0_43, c_0_31])).
% 0.90/1.07  cnf(c_0_50, plain, (X1=X3|X1=X4|X1=X5|X1=X6|X1=X7|~r2_hidden(X1,X2)|X2!=k3_enumset1(X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.90/1.07  fof(c_0_51, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_tarski(X12,X14)|r1_tarski(X12,k3_xboole_0(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.90/1.07  cnf(c_0_52, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk4_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.90/1.07  cnf(c_0_53, negated_conjecture, (v1_relat_1(k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1)))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.90/1.07  cnf(c_0_54, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.90/1.07  cnf(c_0_55, plain, (r2_hidden(X1,k4_enumset1(X2,X2,X3,X4,X5,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_49])])).
% 0.90/1.07  cnf(c_0_56, plain, (X1=X7|X1=X6|X1=X5|X1=X4|X1=X3|X2!=k4_enumset1(X3,X3,X4,X5,X6,X7)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_50, c_0_31])).
% 0.90/1.07  cnf(c_0_57, plain, (r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6)|esk1_6(X1,X2,X3,X4,X5,X6)=X1|esk1_6(X1,X2,X3,X4,X5,X6)=X2|esk1_6(X1,X2,X3,X4,X5,X6)=X3|esk1_6(X1,X2,X3,X4,X5,X6)=X4|esk1_6(X1,X2,X3,X4,X5,X6)=X5|X6=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.90/1.07  cnf(c_0_58, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.90/1.07  cnf(c_0_59, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))),k5_relat_1(esk2_0,esk4_0))|~r1_tarski(k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1)),esk4_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.90/1.07  cnf(c_0_60, plain, (r1_tarski(k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,X5)),X5)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.90/1.07  cnf(c_0_61, negated_conjecture, (~r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.90/1.07  cnf(c_0_62, plain, (X1=X2|X1=X3|X1=X4|X1=X5|X1=X6|~r2_hidden(X1,k4_enumset1(X6,X6,X5,X4,X3,X2))), inference(er,[status(thm)],[c_0_56])).
% 0.90/1.07  cnf(c_0_63, plain, (X6=k4_enumset1(X1,X1,X2,X3,X4,X5)|esk1_6(X1,X2,X3,X4,X5,X6)=X5|esk1_6(X1,X2,X3,X4,X5,X6)=X4|esk1_6(X1,X2,X3,X4,X5,X6)=X3|esk1_6(X1,X2,X3,X4,X5,X6)=X2|esk1_6(X1,X2,X3,X4,X5,X6)=X1|r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6)), inference(rw,[status(thm)],[c_0_57, c_0_31])).
% 0.90/1.07  cnf(c_0_64, plain, (r1_tarski(X1,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_28]), c_0_29]), c_0_30]), c_0_31])).
% 0.90/1.07  cnf(c_0_65, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k5_relat_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.90/1.07  cnf(c_0_66, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk3_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_44, c_0_47])).
% 0.90/1.07  cnf(c_0_67, negated_conjecture, (~r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k4_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31])).
% 0.90/1.07  cnf(c_0_68, plain, (esk1_6(X1,X2,X3,X4,X5,k4_enumset1(X6,X6,X7,X8,X9,X10))=X1|esk1_6(X1,X2,X3,X4,X5,k4_enumset1(X6,X6,X7,X8,X9,X10))=X2|esk1_6(X1,X2,X3,X4,X5,k4_enumset1(X6,X6,X7,X8,X9,X10))=X3|esk1_6(X1,X2,X3,X4,X5,k4_enumset1(X6,X6,X7,X8,X9,X10))=X4|esk1_6(X1,X2,X3,X4,X5,k4_enumset1(X6,X6,X7,X8,X9,X10))=X5|k4_enumset1(X6,X6,X7,X8,X9,X10)=k4_enumset1(X1,X1,X2,X3,X4,X5)|esk1_6(X1,X2,X3,X4,X5,k4_enumset1(X6,X6,X7,X8,X9,X10))=X10|esk1_6(X1,X2,X3,X4,X5,k4_enumset1(X6,X6,X7,X8,X9,X10))=X9|esk1_6(X1,X2,X3,X4,X5,k4_enumset1(X6,X6,X7,X8,X9,X10))=X8|esk1_6(X1,X2,X3,X4,X5,k4_enumset1(X6,X6,X7,X8,X9,X10))=X7|esk1_6(X1,X2,X3,X4,X5,k4_enumset1(X6,X6,X7,X8,X9,X10))=X6), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.90/1.07  cnf(c_0_69, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k4_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),X1)))|~r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),X1)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.90/1.07  cnf(c_0_70, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))),k5_relat_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_53]), c_0_37])])).
% 0.90/1.07  cnf(c_0_71, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.90/1.07  cnf(c_0_72, plain, (X6=k3_enumset1(X1,X2,X3,X4,X5)|esk1_6(X1,X2,X3,X4,X5,X6)!=X5|~r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.90/1.07  cnf(c_0_73, negated_conjecture, (esk1_6(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0),k4_enumset1(X1,X1,X2,X3,X4,X5))=k5_relat_1(esk2_0,esk4_0)|esk1_6(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0),k4_enumset1(X1,X1,X2,X3,X4,X5))=k5_relat_1(esk2_0,esk3_0)|esk1_6(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0),k4_enumset1(X1,X1,X2,X3,X4,X5))=X1|esk1_6(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0),k4_enumset1(X1,X1,X2,X3,X4,X5))=X2|esk1_6(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0),k4_enumset1(X1,X1,X2,X3,X4,X5))=X3|esk1_6(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0),k4_enumset1(X1,X1,X2,X3,X4,X5))=X4|esk1_6(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0),k4_enumset1(X1,X1,X2,X3,X4,X5))=X5|~r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,X5)))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.90/1.07  cnf(c_0_74, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k4_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0))))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.90/1.07  cnf(c_0_75, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X2,X2,X4,X5,X6,X7)), inference(rw,[status(thm)],[c_0_71, c_0_31])).
% 0.90/1.07  cnf(c_0_76, plain, (X6=k3_enumset1(X1,X2,X3,X4,X5)|esk1_6(X1,X2,X3,X4,X5,X6)!=X4|~r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.90/1.07  cnf(c_0_77, plain, (X6=k4_enumset1(X1,X1,X2,X3,X4,X5)|esk1_6(X1,X2,X3,X4,X5,X6)!=X5|~r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6)), inference(rw,[status(thm)],[c_0_72, c_0_31])).
% 0.90/1.07  cnf(c_0_78, negated_conjecture, (esk1_6(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0),k4_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0)))=k5_relat_1(esk2_0,esk3_0)|esk1_6(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0),k4_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0)))=k5_relat_1(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.90/1.07  cnf(c_0_79, plain, (r2_hidden(X1,k4_enumset1(X1,X1,X2,X3,X4,X5))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_75])])).
% 0.90/1.07  cnf(c_0_80, plain, (X6=k4_enumset1(X1,X1,X2,X3,X4,X5)|esk1_6(X1,X2,X3,X4,X5,X6)!=X4|~r2_hidden(esk1_6(X1,X2,X3,X4,X5,X6),X6)), inference(rw,[status(thm)],[c_0_76, c_0_31])).
% 0.90/1.07  cnf(c_0_81, negated_conjecture, (esk1_6(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0),k4_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0)))=k5_relat_1(esk2_0,esk3_0)|k4_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0))=k4_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])])).
% 0.90/1.07  cnf(c_0_82, negated_conjecture, (k4_enumset1(k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk4_0),k5_relat_1(esk2_0,esk3_0))=k4_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_55])])).
% 0.90/1.07  cnf(c_0_83, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_82]), c_0_67]), ['proof']).
% 0.90/1.07  # SZS output end CNFRefutation
% 0.90/1.07  # Proof object total steps             : 84
% 0.90/1.07  # Proof object clause steps            : 55
% 0.90/1.07  # Proof object formula steps           : 29
% 0.90/1.07  # Proof object conjectures             : 23
% 0.90/1.07  # Proof object clause conjectures      : 20
% 0.90/1.07  # Proof object formula conjectures     : 3
% 0.90/1.07  # Proof object initial clauses used    : 22
% 0.90/1.07  # Proof object initial formulas used   : 14
% 0.90/1.07  # Proof object generating inferences   : 18
% 0.90/1.07  # Proof object simplifying inferences  : 39
% 0.90/1.07  # Training examples: 0 positive, 0 negative
% 0.90/1.07  # Parsed axioms                        : 14
% 0.90/1.07  # Removed by relevancy pruning/SinE    : 0
% 0.90/1.07  # Initial clauses                      : 31
% 0.90/1.07  # Removed in clause preprocessing      : 5
% 0.90/1.07  # Initial clauses in saturation        : 26
% 0.90/1.07  # Processed clauses                    : 2662
% 0.90/1.07  # ...of these trivial                  : 59
% 0.90/1.07  # ...subsumed                          : 1096
% 0.90/1.07  # ...remaining for further processing  : 1507
% 0.90/1.07  # Other redundant clauses eliminated   : 196
% 0.90/1.07  # Clauses deleted for lack of memory   : 0
% 0.90/1.07  # Backward-subsumed                    : 163
% 0.90/1.07  # Backward-rewritten                   : 42
% 0.90/1.07  # Generated clauses                    : 18412
% 0.90/1.07  # ...of the previous two non-trivial   : 17492
% 0.90/1.07  # Contextual simplify-reflections      : 1
% 0.90/1.07  # Paramodulations                      : 18045
% 0.90/1.07  # Factorizations                       : 166
% 0.90/1.07  # Equation resolutions                 : 206
% 0.90/1.07  # Propositional unsat checks           : 0
% 0.90/1.07  #    Propositional check models        : 0
% 0.90/1.07  #    Propositional check unsatisfiable : 0
% 0.90/1.07  #    Propositional clauses             : 0
% 0.90/1.07  #    Propositional clauses after purity: 0
% 0.90/1.07  #    Propositional unsat core size     : 0
% 0.90/1.07  #    Propositional preprocessing time  : 0.000
% 0.90/1.07  #    Propositional encoding time       : 0.000
% 0.90/1.07  #    Propositional solver time         : 0.000
% 0.90/1.07  #    Success case prop preproc time    : 0.000
% 0.90/1.07  #    Success case prop encoding time   : 0.000
% 0.90/1.07  #    Success case prop solver time     : 0.000
% 0.90/1.07  # Current number of processed clauses  : 1269
% 0.90/1.07  #    Positive orientable unit clauses  : 208
% 0.90/1.07  #    Positive unorientable unit clauses: 0
% 0.90/1.07  #    Negative unit clauses             : 1
% 0.90/1.07  #    Non-unit-clauses                  : 1060
% 0.90/1.07  # Current number of unprocessed clauses: 14802
% 0.90/1.07  # ...number of literals in the above   : 95232
% 0.90/1.07  # Current number of archived formulas  : 0
% 0.90/1.07  # Current number of archived clauses   : 235
% 0.90/1.07  # Clause-clause subsumption calls (NU) : 379530
% 0.90/1.07  # Rec. Clause-clause subsumption calls : 77092
% 0.90/1.07  # Non-unit clause-clause subsumptions  : 1258
% 0.90/1.07  # Unit Clause-clause subsumption calls : 47407
% 0.90/1.07  # Rewrite failures with RHS unbound    : 0
% 0.90/1.07  # BW rewrite match attempts            : 1915
% 0.90/1.07  # BW rewrite match successes           : 39
% 0.90/1.07  # Condensation attempts                : 0
% 0.90/1.07  # Condensation successes               : 0
% 0.90/1.07  # Termbank termtop insertions          : 1960854
% 0.90/1.07  
% 0.90/1.07  # -------------------------------------------------
% 0.90/1.07  # User time                : 0.710 s
% 0.90/1.07  # System time              : 0.016 s
% 0.90/1.07  # Total time               : 0.726 s
% 0.90/1.07  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
