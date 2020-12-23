%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:39 EST 2020

% Result     : Theorem 6.09s
% Output     : CNFRefutation 6.09s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 164 expanded)
%              Number of clauses        :   40 (  73 expanded)
%              Number of leaves         :   13 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  202 ( 604 expanded)
%              Number of equality atoms :   70 ( 246 expanded)
%              Maximal formula depth    :   37 (   4 average)
%              Maximal clause size      :   52 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] :
      ( X7 = k4_enumset1(X1,X2,X3,X4,X5,X6)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X8 != X1
              & X8 != X2
              & X8 != X3
              & X8 != X4
              & X8 != X5
              & X8 != X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

fof(t52_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

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

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(c_0_13,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36,X37,X38,X39,X40,X41,X42,X43,X44,X45] :
      ( ( ~ r2_hidden(X37,X36)
        | X37 = X30
        | X37 = X31
        | X37 = X32
        | X37 = X33
        | X37 = X34
        | X37 = X35
        | X36 != k4_enumset1(X30,X31,X32,X33,X34,X35) )
      & ( X38 != X30
        | r2_hidden(X38,X36)
        | X36 != k4_enumset1(X30,X31,X32,X33,X34,X35) )
      & ( X38 != X31
        | r2_hidden(X38,X36)
        | X36 != k4_enumset1(X30,X31,X32,X33,X34,X35) )
      & ( X38 != X32
        | r2_hidden(X38,X36)
        | X36 != k4_enumset1(X30,X31,X32,X33,X34,X35) )
      & ( X38 != X33
        | r2_hidden(X38,X36)
        | X36 != k4_enumset1(X30,X31,X32,X33,X34,X35) )
      & ( X38 != X34
        | r2_hidden(X38,X36)
        | X36 != k4_enumset1(X30,X31,X32,X33,X34,X35) )
      & ( X38 != X35
        | r2_hidden(X38,X36)
        | X36 != k4_enumset1(X30,X31,X32,X33,X34,X35) )
      & ( esk1_7(X39,X40,X41,X42,X43,X44,X45) != X39
        | ~ r2_hidden(esk1_7(X39,X40,X41,X42,X43,X44,X45),X45)
        | X45 = k4_enumset1(X39,X40,X41,X42,X43,X44) )
      & ( esk1_7(X39,X40,X41,X42,X43,X44,X45) != X40
        | ~ r2_hidden(esk1_7(X39,X40,X41,X42,X43,X44,X45),X45)
        | X45 = k4_enumset1(X39,X40,X41,X42,X43,X44) )
      & ( esk1_7(X39,X40,X41,X42,X43,X44,X45) != X41
        | ~ r2_hidden(esk1_7(X39,X40,X41,X42,X43,X44,X45),X45)
        | X45 = k4_enumset1(X39,X40,X41,X42,X43,X44) )
      & ( esk1_7(X39,X40,X41,X42,X43,X44,X45) != X42
        | ~ r2_hidden(esk1_7(X39,X40,X41,X42,X43,X44,X45),X45)
        | X45 = k4_enumset1(X39,X40,X41,X42,X43,X44) )
      & ( esk1_7(X39,X40,X41,X42,X43,X44,X45) != X43
        | ~ r2_hidden(esk1_7(X39,X40,X41,X42,X43,X44,X45),X45)
        | X45 = k4_enumset1(X39,X40,X41,X42,X43,X44) )
      & ( esk1_7(X39,X40,X41,X42,X43,X44,X45) != X44
        | ~ r2_hidden(esk1_7(X39,X40,X41,X42,X43,X44,X45),X45)
        | X45 = k4_enumset1(X39,X40,X41,X42,X43,X44) )
      & ( r2_hidden(esk1_7(X39,X40,X41,X42,X43,X44,X45),X45)
        | esk1_7(X39,X40,X41,X42,X43,X44,X45) = X39
        | esk1_7(X39,X40,X41,X42,X43,X44,X45) = X40
        | esk1_7(X39,X40,X41,X42,X43,X44,X45) = X41
        | esk1_7(X39,X40,X41,X42,X43,X44,X45) = X42
        | esk1_7(X39,X40,X41,X42,X43,X44,X45) = X43
        | esk1_7(X39,X40,X41,X42,X43,X44,X45) = X44
        | X45 = k4_enumset1(X39,X40,X41,X42,X43,X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relat_1])).

fof(c_0_15,plain,(
    ! [X51,X52] :
      ( ~ r2_hidden(X51,X52)
      | r1_tarski(k1_setfam_1(X52),X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X4,X5,X6,X7,X8,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X55,X56,X57,X58] :
      ( ~ v1_relat_1(X55)
      | ~ v1_relat_1(X56)
      | ~ v1_relat_1(X57)
      | ~ v1_relat_1(X58)
      | ~ r1_tarski(X55,X56)
      | ~ r1_tarski(X57,X58)
      | r1_tarski(k5_relat_1(X55,X57),k5_relat_1(X56,X58)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_relat_1])])])).

fof(c_0_18,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & ~ r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_19,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_20,plain,(
    ! [X49,X50] :
      ( ( ~ m1_subset_1(X49,k1_zfmisc_1(X50))
        | r1_tarski(X49,X50) )
      & ( ~ r1_tarski(X49,X50)
        | m1_subset_1(X49,k1_zfmisc_1(X50)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_21,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k4_enumset1(X2,X3,X4,X5,X6,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_16])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X4,X5,X6,X7,X2,X8) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X53,X54] :
      ( ~ v1_relat_1(X53)
      | ~ m1_subset_1(X54,k1_zfmisc_1(X53))
      | v1_relat_1(X54) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,X6)),X6) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k4_enumset1(X2,X3,X4,X5,X1,X6)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).

fof(c_0_31,plain,(
    ! [X47,X48] : k1_setfam_1(k2_tarski(X47,X48)) = k3_xboole_0(X47,X48) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_32,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(esk2_0,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( m1_subset_1(k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,X6)),k1_zfmisc_1(X6)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,X6)),X5) ),
    inference(spm,[status(thm)],[c_0_21,c_0_30])).

fof(c_0_38,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X13,X15)
      | r1_tarski(X13,k3_xboole_0(X14,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_39,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_41,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_42,plain,(
    ! [X21,X22,X23,X24] : k3_enumset1(X21,X21,X22,X23,X24) = k2_enumset1(X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_43,plain,(
    ! [X25,X26,X27,X28,X29] : k4_enumset1(X25,X25,X26,X27,X28,X29) = k3_enumset1(X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_25]),c_0_34])])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_46,plain,
    ( v1_relat_1(k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,X6)))
    | ~ v1_relat_1(X6) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_47,plain,
    ( m1_subset_1(k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,X6)),k1_zfmisc_1(X5)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_37])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk4_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( v1_relat_1(k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_56,plain,
    ( v1_relat_1(k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,X6)))
    | ~ v1_relat_1(X5) ),
    inference(spm,[status(thm)],[c_0_35,c_0_47])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,esk4_0))),k5_relat_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_29])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk3_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( v1_relat_1(k1_setfam_1(k4_enumset1(X1,X2,X3,X4,esk3_0,X5))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,esk4_0))),k1_setfam_1(k4_enumset1(X6,X6,X6,X6,X6,k5_relat_1(esk2_0,esk4_0))))
    | ~ r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,esk4_0))),X6) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(X1,X2,X3,X4,esk3_0,X5))),k5_relat_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_37])])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k4_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(X1,X2,X3,X4,esk3_0,esk4_0))),k1_setfam_1(k4_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:56:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 6.09/6.33  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S002I
% 6.09/6.33  # and selection function SelectNegativeLiterals.
% 6.09/6.33  #
% 6.09/6.33  # Preprocessing time       : 0.028 s
% 6.09/6.33  # Presaturation interreduction done
% 6.09/6.33  
% 6.09/6.33  # Proof found!
% 6.09/6.33  # SZS status Theorem
% 6.09/6.33  # SZS output start CNFRefutation
% 6.09/6.33  fof(d4_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:(X7=k4_enumset1(X1,X2,X3,X4,X5,X6)<=>![X8]:(r2_hidden(X8,X7)<=>~((((((X8!=X1&X8!=X2)&X8!=X3)&X8!=X4)&X8!=X5)&X8!=X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 6.09/6.33  fof(t52_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 6.09/6.33  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 6.09/6.33  fof(t50_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relat_1)).
% 6.09/6.33  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.09/6.33  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.09/6.33  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.09/6.33  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 6.09/6.33  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.09/6.33  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 6.09/6.33  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 6.09/6.33  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 6.09/6.33  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 6.09/6.33  fof(c_0_13, plain, ![X30, X31, X32, X33, X34, X35, X36, X37, X38, X39, X40, X41, X42, X43, X44, X45]:(((~r2_hidden(X37,X36)|(X37=X30|X37=X31|X37=X32|X37=X33|X37=X34|X37=X35)|X36!=k4_enumset1(X30,X31,X32,X33,X34,X35))&((((((X38!=X30|r2_hidden(X38,X36)|X36!=k4_enumset1(X30,X31,X32,X33,X34,X35))&(X38!=X31|r2_hidden(X38,X36)|X36!=k4_enumset1(X30,X31,X32,X33,X34,X35)))&(X38!=X32|r2_hidden(X38,X36)|X36!=k4_enumset1(X30,X31,X32,X33,X34,X35)))&(X38!=X33|r2_hidden(X38,X36)|X36!=k4_enumset1(X30,X31,X32,X33,X34,X35)))&(X38!=X34|r2_hidden(X38,X36)|X36!=k4_enumset1(X30,X31,X32,X33,X34,X35)))&(X38!=X35|r2_hidden(X38,X36)|X36!=k4_enumset1(X30,X31,X32,X33,X34,X35))))&(((((((esk1_7(X39,X40,X41,X42,X43,X44,X45)!=X39|~r2_hidden(esk1_7(X39,X40,X41,X42,X43,X44,X45),X45)|X45=k4_enumset1(X39,X40,X41,X42,X43,X44))&(esk1_7(X39,X40,X41,X42,X43,X44,X45)!=X40|~r2_hidden(esk1_7(X39,X40,X41,X42,X43,X44,X45),X45)|X45=k4_enumset1(X39,X40,X41,X42,X43,X44)))&(esk1_7(X39,X40,X41,X42,X43,X44,X45)!=X41|~r2_hidden(esk1_7(X39,X40,X41,X42,X43,X44,X45),X45)|X45=k4_enumset1(X39,X40,X41,X42,X43,X44)))&(esk1_7(X39,X40,X41,X42,X43,X44,X45)!=X42|~r2_hidden(esk1_7(X39,X40,X41,X42,X43,X44,X45),X45)|X45=k4_enumset1(X39,X40,X41,X42,X43,X44)))&(esk1_7(X39,X40,X41,X42,X43,X44,X45)!=X43|~r2_hidden(esk1_7(X39,X40,X41,X42,X43,X44,X45),X45)|X45=k4_enumset1(X39,X40,X41,X42,X43,X44)))&(esk1_7(X39,X40,X41,X42,X43,X44,X45)!=X44|~r2_hidden(esk1_7(X39,X40,X41,X42,X43,X44,X45),X45)|X45=k4_enumset1(X39,X40,X41,X42,X43,X44)))&(r2_hidden(esk1_7(X39,X40,X41,X42,X43,X44,X45),X45)|(esk1_7(X39,X40,X41,X42,X43,X44,X45)=X39|esk1_7(X39,X40,X41,X42,X43,X44,X45)=X40|esk1_7(X39,X40,X41,X42,X43,X44,X45)=X41|esk1_7(X39,X40,X41,X42,X43,X44,X45)=X42|esk1_7(X39,X40,X41,X42,X43,X44,X45)=X43|esk1_7(X39,X40,X41,X42,X43,X44,X45)=X44)|X45=k4_enumset1(X39,X40,X41,X42,X43,X44)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).
% 6.09/6.33  fof(c_0_14, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t52_relat_1])).
% 6.09/6.33  fof(c_0_15, plain, ![X51, X52]:(~r2_hidden(X51,X52)|r1_tarski(k1_setfam_1(X52),X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 6.09/6.33  cnf(c_0_16, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X4,X5,X6,X7,X8,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 6.09/6.33  fof(c_0_17, plain, ![X55, X56, X57, X58]:(~v1_relat_1(X55)|(~v1_relat_1(X56)|(~v1_relat_1(X57)|(~v1_relat_1(X58)|(~r1_tarski(X55,X56)|~r1_tarski(X57,X58)|r1_tarski(k5_relat_1(X55,X57),k5_relat_1(X56,X58))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_relat_1])])])).
% 6.09/6.33  fof(c_0_18, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&~r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 6.09/6.33  fof(c_0_19, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 6.09/6.33  fof(c_0_20, plain, ![X49, X50]:((~m1_subset_1(X49,k1_zfmisc_1(X50))|r1_tarski(X49,X50))&(~r1_tarski(X49,X50)|m1_subset_1(X49,k1_zfmisc_1(X50)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 6.09/6.33  cnf(c_0_21, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 6.09/6.33  cnf(c_0_22, plain, (r2_hidden(X1,k4_enumset1(X2,X3,X4,X5,X6,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_16])])).
% 6.09/6.33  cnf(c_0_23, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X4,X5,X6,X7,X2,X8)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 6.09/6.33  cnf(c_0_24, plain, (r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~v1_relat_1(X4)|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 6.09/6.33  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 6.09/6.33  cnf(c_0_26, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 6.09/6.33  fof(c_0_27, plain, ![X53, X54]:(~v1_relat_1(X53)|(~m1_subset_1(X54,k1_zfmisc_1(X53))|v1_relat_1(X54))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 6.09/6.33  cnf(c_0_28, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 6.09/6.33  cnf(c_0_29, plain, (r1_tarski(k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,X6)),X6)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 6.09/6.33  cnf(c_0_30, plain, (r2_hidden(X1,k4_enumset1(X2,X3,X4,X5,X1,X6))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).
% 6.09/6.33  fof(c_0_31, plain, ![X47, X48]:k1_setfam_1(k2_tarski(X47,X48))=k3_xboole_0(X47,X48), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 6.09/6.33  fof(c_0_32, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 6.09/6.33  cnf(c_0_33, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(X2,X3))|~v1_relat_1(X3)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(esk2_0,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 6.09/6.33  cnf(c_0_34, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_26])).
% 6.09/6.33  cnf(c_0_35, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 6.09/6.33  cnf(c_0_36, plain, (m1_subset_1(k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,X6)),k1_zfmisc_1(X6))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 6.09/6.33  cnf(c_0_37, plain, (r1_tarski(k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,X6)),X5)), inference(spm,[status(thm)],[c_0_21, c_0_30])).
% 6.09/6.33  fof(c_0_38, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X13,X15)|r1_tarski(X13,k3_xboole_0(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 6.09/6.33  cnf(c_0_39, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 6.09/6.33  cnf(c_0_40, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 6.09/6.33  fof(c_0_41, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 6.09/6.33  fof(c_0_42, plain, ![X21, X22, X23, X24]:k3_enumset1(X21,X21,X22,X23,X24)=k2_enumset1(X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 6.09/6.33  fof(c_0_43, plain, ![X25, X26, X27, X28, X29]:k4_enumset1(X25,X25,X26,X27,X28,X29)=k3_enumset1(X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 6.09/6.33  cnf(c_0_44, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_25]), c_0_34])])).
% 6.09/6.33  cnf(c_0_45, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 6.09/6.33  cnf(c_0_46, plain, (v1_relat_1(k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,X6)))|~v1_relat_1(X6)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 6.09/6.33  cnf(c_0_47, plain, (m1_subset_1(k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,X6)),k1_zfmisc_1(X5))), inference(spm,[status(thm)],[c_0_28, c_0_37])).
% 6.09/6.33  cnf(c_0_48, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 6.09/6.33  cnf(c_0_49, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 6.09/6.33  cnf(c_0_50, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 6.09/6.33  cnf(c_0_51, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 6.09/6.33  cnf(c_0_52, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 6.09/6.33  cnf(c_0_53, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk4_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 6.09/6.33  cnf(c_0_54, negated_conjecture, (v1_relat_1(k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,esk4_0)))), inference(spm,[status(thm)],[c_0_46, c_0_45])).
% 6.09/6.33  cnf(c_0_55, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 6.09/6.33  cnf(c_0_56, plain, (v1_relat_1(k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,X6)))|~v1_relat_1(X5)), inference(spm,[status(thm)],[c_0_35, c_0_47])).
% 6.09/6.33  cnf(c_0_57, plain, (r1_tarski(X1,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51]), c_0_52])).
% 6.09/6.33  cnf(c_0_58, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,esk4_0))),k5_relat_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_29])])).
% 6.09/6.33  cnf(c_0_59, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk3_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_44, c_0_55])).
% 6.09/6.33  cnf(c_0_60, negated_conjecture, (v1_relat_1(k1_setfam_1(k4_enumset1(X1,X2,X3,X4,esk3_0,X5)))), inference(spm,[status(thm)],[c_0_56, c_0_55])).
% 6.09/6.33  cnf(c_0_61, negated_conjecture, (~r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 6.09/6.33  cnf(c_0_62, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,esk4_0))),k1_setfam_1(k4_enumset1(X6,X6,X6,X6,X6,k5_relat_1(esk2_0,esk4_0))))|~r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,esk4_0))),X6)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 6.09/6.33  cnf(c_0_63, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(X1,X2,X3,X4,esk3_0,X5))),k5_relat_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_37])])).
% 6.09/6.33  cnf(c_0_64, negated_conjecture, (~r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k4_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_52]), c_0_52])).
% 6.09/6.33  cnf(c_0_65, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k4_enumset1(X1,X2,X3,X4,esk3_0,esk4_0))),k1_setfam_1(k4_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 6.09/6.33  cnf(c_0_66, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65])]), ['proof']).
% 6.09/6.33  # SZS output end CNFRefutation
% 6.09/6.33  # Proof object total steps             : 67
% 6.09/6.33  # Proof object clause steps            : 40
% 6.09/6.33  # Proof object formula steps           : 27
% 6.09/6.33  # Proof object conjectures             : 19
% 6.09/6.33  # Proof object clause conjectures      : 16
% 6.09/6.33  # Proof object formula conjectures     : 3
% 6.09/6.33  # Proof object initial clauses used    : 17
% 6.09/6.33  # Proof object initial formulas used   : 13
% 6.09/6.33  # Proof object generating inferences   : 16
% 6.09/6.33  # Proof object simplifying inferences  : 26
% 6.09/6.33  # Training examples: 0 positive, 0 negative
% 6.09/6.33  # Parsed axioms                        : 14
% 6.09/6.33  # Removed by relevancy pruning/SinE    : 0
% 6.09/6.33  # Initial clauses                      : 33
% 6.09/6.33  # Removed in clause preprocessing      : 5
% 6.09/6.33  # Initial clauses in saturation        : 28
% 6.09/6.33  # Processed clauses                    : 9355
% 6.09/6.33  # ...of these trivial                  : 239
% 6.09/6.33  # ...subsumed                          : 5582
% 6.09/6.33  # ...remaining for further processing  : 3534
% 6.09/6.33  # Other redundant clauses eliminated   : 11433
% 6.09/6.33  # Clauses deleted for lack of memory   : 0
% 6.09/6.33  # Backward-subsumed                    : 1
% 6.09/6.33  # Backward-rewritten                   : 30
% 6.09/6.33  # Generated clauses                    : 273394
% 6.09/6.33  # ...of the previous two non-trivial   : 250548
% 6.09/6.33  # Contextual simplify-reflections      : 0
% 6.09/6.33  # Paramodulations                      : 254575
% 6.09/6.33  # Factorizations                       : 7392
% 6.09/6.33  # Equation resolutions                 : 11433
% 6.09/6.33  # Propositional unsat checks           : 0
% 6.09/6.33  #    Propositional check models        : 0
% 6.09/6.33  #    Propositional check unsatisfiable : 0
% 6.09/6.33  #    Propositional clauses             : 0
% 6.09/6.33  #    Propositional clauses after purity: 0
% 6.09/6.33  #    Propositional unsat core size     : 0
% 6.09/6.33  #    Propositional preprocessing time  : 0.000
% 6.09/6.33  #    Propositional encoding time       : 0.000
% 6.09/6.33  #    Propositional solver time         : 0.000
% 6.09/6.33  #    Success case prop preproc time    : 0.000
% 6.09/6.33  #    Success case prop encoding time   : 0.000
% 6.09/6.33  #    Success case prop solver time     : 0.000
% 6.09/6.33  # Current number of processed clauses  : 3467
% 6.09/6.33  #    Positive orientable unit clauses  : 466
% 6.09/6.33  #    Positive unorientable unit clauses: 0
% 6.09/6.33  #    Negative unit clauses             : 0
% 6.09/6.33  #    Non-unit-clauses                  : 3001
% 6.09/6.33  # Current number of unprocessed clauses: 241223
% 6.09/6.33  # ...number of literals in the above   : 851852
% 6.09/6.33  # Current number of archived formulas  : 0
% 6.09/6.33  # Current number of archived clauses   : 63
% 6.09/6.33  # Clause-clause subsumption calls (NU) : 2478094
% 6.09/6.33  # Rec. Clause-clause subsumption calls : 1570610
% 6.09/6.33  # Non-unit clause-clause subsumptions  : 5583
% 6.09/6.33  # Unit Clause-clause subsumption calls : 144537
% 6.09/6.33  # Rewrite failures with RHS unbound    : 0
% 6.09/6.33  # BW rewrite match attempts            : 12357
% 6.09/6.33  # BW rewrite match successes           : 11
% 6.09/6.33  # Condensation attempts                : 0
% 6.09/6.33  # Condensation successes               : 0
% 6.09/6.33  # Termbank termtop insertions          : 7805852
% 6.09/6.34  
% 6.09/6.34  # -------------------------------------------------
% 6.09/6.34  # User time                : 5.891 s
% 6.09/6.34  # System time              : 0.107 s
% 6.09/6.34  # Total time               : 5.998 s
% 6.09/6.34  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
