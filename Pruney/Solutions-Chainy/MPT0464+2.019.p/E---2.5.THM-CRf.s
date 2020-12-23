%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:40 EST 2020

% Result     : Theorem 0.76s
% Output     : CNFRefutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 157 expanded)
%              Number of clauses        :   41 (  74 expanded)
%              Number of leaves         :   11 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  170 ( 479 expanded)
%              Number of equality atoms :   54 ( 195 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( X5 = k2_enumset1(X1,X2,X3,X4)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X6 != X1
              & X6 != X2
              & X6 != X3
              & X6 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t52_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(t48_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( r1_tarski(X1,X2)
               => r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(c_0_11,plain,(
    ! [X21,X22,X23,X24,X25,X26,X27,X28,X29,X30,X31,X32] :
      ( ( ~ r2_hidden(X26,X25)
        | X26 = X21
        | X26 = X22
        | X26 = X23
        | X26 = X24
        | X25 != k2_enumset1(X21,X22,X23,X24) )
      & ( X27 != X21
        | r2_hidden(X27,X25)
        | X25 != k2_enumset1(X21,X22,X23,X24) )
      & ( X27 != X22
        | r2_hidden(X27,X25)
        | X25 != k2_enumset1(X21,X22,X23,X24) )
      & ( X27 != X23
        | r2_hidden(X27,X25)
        | X25 != k2_enumset1(X21,X22,X23,X24) )
      & ( X27 != X24
        | r2_hidden(X27,X25)
        | X25 != k2_enumset1(X21,X22,X23,X24) )
      & ( esk1_5(X28,X29,X30,X31,X32) != X28
        | ~ r2_hidden(esk1_5(X28,X29,X30,X31,X32),X32)
        | X32 = k2_enumset1(X28,X29,X30,X31) )
      & ( esk1_5(X28,X29,X30,X31,X32) != X29
        | ~ r2_hidden(esk1_5(X28,X29,X30,X31,X32),X32)
        | X32 = k2_enumset1(X28,X29,X30,X31) )
      & ( esk1_5(X28,X29,X30,X31,X32) != X30
        | ~ r2_hidden(esk1_5(X28,X29,X30,X31,X32),X32)
        | X32 = k2_enumset1(X28,X29,X30,X31) )
      & ( esk1_5(X28,X29,X30,X31,X32) != X31
        | ~ r2_hidden(esk1_5(X28,X29,X30,X31,X32),X32)
        | X32 = k2_enumset1(X28,X29,X30,X31) )
      & ( r2_hidden(esk1_5(X28,X29,X30,X31,X32),X32)
        | esk1_5(X28,X29,X30,X31,X32) = X28
        | esk1_5(X28,X29,X30,X31,X32) = X29
        | esk1_5(X28,X29,X30,X31,X32) = X30
        | esk1_5(X28,X29,X30,X31,X32) = X31
        | X32 = k2_enumset1(X28,X29,X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).

fof(c_0_12,plain,(
    ! [X17,X18,X19,X20] : k3_enumset1(X17,X17,X18,X19,X20) = k2_enumset1(X17,X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X5,X6,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relat_1])).

fof(c_0_18,plain,(
    ! [X38,X39] :
      ( ~ r2_hidden(X38,X39)
      | r1_tarski(k1_setfam_1(X39),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | X2 != k3_enumset1(X3,X3,X4,X5,X1) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X4,X5,X6) ),
    inference(rw,[status(thm)],[c_0_16,c_0_14])).

fof(c_0_21,plain,(
    ! [X42,X43,X44] :
      ( ~ v1_relat_1(X42)
      | ~ v1_relat_1(X43)
      | ~ v1_relat_1(X44)
      | ~ r1_tarski(X42,X43)
      | r1_tarski(k5_relat_1(X44,X42),k5_relat_1(X44,X43)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & ~ r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_23,plain,(
    ! [X40,X41] :
      ( ~ v1_relat_1(X40)
      | ~ m1_subset_1(X41,k1_zfmisc_1(X40))
      | v1_relat_1(X41) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_24,plain,(
    ! [X36,X37] :
      ( ( ~ m1_subset_1(X36,k1_zfmisc_1(X37))
        | r1_tarski(X36,X37) )
      & ( ~ r1_tarski(X36,X37)
        | m1_subset_1(X36,k1_zfmisc_1(X37)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X3,X4,X1)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | X2 != k3_enumset1(X1,X1,X3,X4,X5) ),
    inference(er,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X34,X35] : k1_setfam_1(k2_tarski(X34,X35)) = k3_xboole_0(X34,X35) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_29,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_30,plain,
    ( r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r1_tarski(k1_setfam_1(k3_enumset1(X1,X1,X2,X3,X4)),X4) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_27])).

fof(c_0_36,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | ~ r1_tarski(X9,X11)
      | r1_tarski(X9,k3_xboole_0(X10,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_37,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_39,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,esk4_0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X2,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

cnf(c_0_43,plain,
    ( m1_subset_1(k1_setfam_1(k3_enumset1(X1,X1,X2,X3,X4)),k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_setfam_1(k3_enumset1(X1,X1,X2,X3,X4)),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_35])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_48,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk4_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( v1_relat_1(k1_setfam_1(k3_enumset1(X1,X1,X2,X3,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,esk3_0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_44])).

cnf(c_0_53,plain,
    ( m1_subset_1(k1_setfam_1(k3_enumset1(X1,X1,X2,X3,X4)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_45])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_14])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k3_enumset1(X1,X1,X2,X3,esk4_0))),k5_relat_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_34])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk3_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_41])).

cnf(c_0_57,negated_conjecture,
    ( v1_relat_1(k1_setfam_1(k3_enumset1(esk3_0,esk3_0,X1,X2,X3))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k3_enumset1(X1,X1,X2,X3,esk4_0))),k1_setfam_1(k3_enumset1(X4,X4,X4,X4,k5_relat_1(esk2_0,esk4_0))))
    | ~ r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k3_enumset1(X1,X1,X2,X3,esk4_0))),X4) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k3_enumset1(esk3_0,esk3_0,X1,X2,X3))),k5_relat_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_45])])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k3_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_14]),c_0_14])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k3_enumset1(esk3_0,esk3_0,X1,X2,esk4_0))),k1_setfam_1(k3_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.76/0.94  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S002A
% 0.76/0.94  # and selection function SelectNegativeLiterals.
% 0.76/0.94  #
% 0.76/0.94  # Preprocessing time       : 0.023 s
% 0.76/0.94  # Presaturation interreduction done
% 0.76/0.94  
% 0.76/0.94  # Proof found!
% 0.76/0.94  # SZS status Theorem
% 0.76/0.94  # SZS output start CNFRefutation
% 0.76/0.94  fof(d2_enumset1, axiom, ![X1, X2, X3, X4, X5]:(X5=k2_enumset1(X1,X2,X3,X4)<=>![X6]:(r2_hidden(X6,X5)<=>~((((X6!=X1&X6!=X2)&X6!=X3)&X6!=X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 0.76/0.94  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.76/0.94  fof(t52_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 0.76/0.94  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.76/0.94  fof(t48_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 0.76/0.94  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.76/0.94  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.76/0.94  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.76/0.94  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.76/0.94  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.76/0.94  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.76/0.94  fof(c_0_11, plain, ![X21, X22, X23, X24, X25, X26, X27, X28, X29, X30, X31, X32]:(((~r2_hidden(X26,X25)|(X26=X21|X26=X22|X26=X23|X26=X24)|X25!=k2_enumset1(X21,X22,X23,X24))&((((X27!=X21|r2_hidden(X27,X25)|X25!=k2_enumset1(X21,X22,X23,X24))&(X27!=X22|r2_hidden(X27,X25)|X25!=k2_enumset1(X21,X22,X23,X24)))&(X27!=X23|r2_hidden(X27,X25)|X25!=k2_enumset1(X21,X22,X23,X24)))&(X27!=X24|r2_hidden(X27,X25)|X25!=k2_enumset1(X21,X22,X23,X24))))&(((((esk1_5(X28,X29,X30,X31,X32)!=X28|~r2_hidden(esk1_5(X28,X29,X30,X31,X32),X32)|X32=k2_enumset1(X28,X29,X30,X31))&(esk1_5(X28,X29,X30,X31,X32)!=X29|~r2_hidden(esk1_5(X28,X29,X30,X31,X32),X32)|X32=k2_enumset1(X28,X29,X30,X31)))&(esk1_5(X28,X29,X30,X31,X32)!=X30|~r2_hidden(esk1_5(X28,X29,X30,X31,X32),X32)|X32=k2_enumset1(X28,X29,X30,X31)))&(esk1_5(X28,X29,X30,X31,X32)!=X31|~r2_hidden(esk1_5(X28,X29,X30,X31,X32),X32)|X32=k2_enumset1(X28,X29,X30,X31)))&(r2_hidden(esk1_5(X28,X29,X30,X31,X32),X32)|(esk1_5(X28,X29,X30,X31,X32)=X28|esk1_5(X28,X29,X30,X31,X32)=X29|esk1_5(X28,X29,X30,X31,X32)=X30|esk1_5(X28,X29,X30,X31,X32)=X31)|X32=k2_enumset1(X28,X29,X30,X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).
% 0.76/0.94  fof(c_0_12, plain, ![X17, X18, X19, X20]:k3_enumset1(X17,X17,X18,X19,X20)=k2_enumset1(X17,X18,X19,X20), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.76/0.94  cnf(c_0_13, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X5,X6,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.76/0.94  cnf(c_0_14, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.76/0.94  cnf(c_0_15, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X5,X6,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.76/0.94  cnf(c_0_16, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.76/0.94  fof(c_0_17, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t52_relat_1])).
% 0.76/0.94  fof(c_0_18, plain, ![X38, X39]:(~r2_hidden(X38,X39)|r1_tarski(k1_setfam_1(X39),X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.76/0.94  cnf(c_0_19, plain, (r2_hidden(X1,X2)|X2!=k3_enumset1(X3,X3,X4,X5,X1)), inference(er,[status(thm)],[c_0_15])).
% 0.76/0.94  cnf(c_0_20, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X4,X5,X6)), inference(rw,[status(thm)],[c_0_16, c_0_14])).
% 0.76/0.94  fof(c_0_21, plain, ![X42, X43, X44]:(~v1_relat_1(X42)|(~v1_relat_1(X43)|(~v1_relat_1(X44)|(~r1_tarski(X42,X43)|r1_tarski(k5_relat_1(X44,X42),k5_relat_1(X44,X43)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).
% 0.76/0.94  fof(c_0_22, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&~r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.76/0.94  fof(c_0_23, plain, ![X40, X41]:(~v1_relat_1(X40)|(~m1_subset_1(X41,k1_zfmisc_1(X40))|v1_relat_1(X41))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.76/0.94  fof(c_0_24, plain, ![X36, X37]:((~m1_subset_1(X36,k1_zfmisc_1(X37))|r1_tarski(X36,X37))&(~r1_tarski(X36,X37)|m1_subset_1(X36,k1_zfmisc_1(X37)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.76/0.94  cnf(c_0_25, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.76/0.94  cnf(c_0_26, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X3,X4,X1))), inference(er,[status(thm)],[c_0_19])).
% 0.76/0.94  cnf(c_0_27, plain, (r2_hidden(X1,X2)|X2!=k3_enumset1(X1,X1,X3,X4,X5)), inference(er,[status(thm)],[c_0_20])).
% 0.76/0.94  fof(c_0_28, plain, ![X34, X35]:k1_setfam_1(k2_tarski(X34,X35))=k3_xboole_0(X34,X35), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.76/0.94  fof(c_0_29, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.76/0.94  cnf(c_0_30, plain, (r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.76/0.94  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.76/0.94  cnf(c_0_32, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.76/0.94  cnf(c_0_33, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.76/0.94  cnf(c_0_34, plain, (r1_tarski(k1_setfam_1(k3_enumset1(X1,X1,X2,X3,X4)),X4)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.76/0.94  cnf(c_0_35, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X2,X3,X4))), inference(er,[status(thm)],[c_0_27])).
% 0.76/0.94  fof(c_0_36, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|~r1_tarski(X9,X11)|r1_tarski(X9,k3_xboole_0(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.76/0.94  cnf(c_0_37, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.76/0.94  cnf(c_0_38, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.76/0.94  fof(c_0_39, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.76/0.94  cnf(c_0_40, negated_conjecture, (r1_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,esk4_0))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X2,esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.76/0.94  cnf(c_0_41, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.76/0.94  cnf(c_0_42, negated_conjecture, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_32, c_0_31])).
% 0.76/0.94  cnf(c_0_43, plain, (m1_subset_1(k1_setfam_1(k3_enumset1(X1,X1,X2,X3,X4)),k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.76/0.94  cnf(c_0_44, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.76/0.94  cnf(c_0_45, plain, (r1_tarski(k1_setfam_1(k3_enumset1(X1,X1,X2,X3,X4)),X1)), inference(spm,[status(thm)],[c_0_25, c_0_35])).
% 0.76/0.94  cnf(c_0_46, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.76/0.94  cnf(c_0_47, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.76/0.94  cnf(c_0_48, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.76/0.94  cnf(c_0_49, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk4_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.76/0.94  cnf(c_0_50, negated_conjecture, (v1_relat_1(k1_setfam_1(k3_enumset1(X1,X1,X2,X3,esk4_0)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.76/0.94  cnf(c_0_51, negated_conjecture, (r1_tarski(k5_relat_1(X1,X2),k5_relat_1(X1,esk3_0))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X2,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_44])).
% 0.76/0.94  cnf(c_0_52, negated_conjecture, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_44])).
% 0.76/0.94  cnf(c_0_53, plain, (m1_subset_1(k1_setfam_1(k3_enumset1(X1,X1,X2,X3,X4)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_33, c_0_45])).
% 0.76/0.94  cnf(c_0_54, plain, (r1_tarski(X1,k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_14])).
% 0.76/0.94  cnf(c_0_55, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k3_enumset1(X1,X1,X2,X3,esk4_0))),k5_relat_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_34])])).
% 0.76/0.94  cnf(c_0_56, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,X1),k5_relat_1(esk2_0,esk3_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_51, c_0_41])).
% 0.76/0.94  cnf(c_0_57, negated_conjecture, (v1_relat_1(k1_setfam_1(k3_enumset1(esk3_0,esk3_0,X1,X2,X3)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.76/0.94  cnf(c_0_58, negated_conjecture, (~r1_tarski(k5_relat_1(esk2_0,k3_xboole_0(esk3_0,esk4_0)),k3_xboole_0(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.76/0.94  cnf(c_0_59, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k3_enumset1(X1,X1,X2,X3,esk4_0))),k1_setfam_1(k3_enumset1(X4,X4,X4,X4,k5_relat_1(esk2_0,esk4_0))))|~r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k3_enumset1(X1,X1,X2,X3,esk4_0))),X4)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.76/0.94  cnf(c_0_60, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k3_enumset1(esk3_0,esk3_0,X1,X2,X3))),k5_relat_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_45])])).
% 0.76/0.94  cnf(c_0_61, negated_conjecture, (~r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))),k1_setfam_1(k3_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_14]), c_0_14])).
% 0.76/0.94  cnf(c_0_62, negated_conjecture, (r1_tarski(k5_relat_1(esk2_0,k1_setfam_1(k3_enumset1(esk3_0,esk3_0,X1,X2,esk4_0))),k1_setfam_1(k3_enumset1(k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk3_0),k5_relat_1(esk2_0,esk4_0))))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.76/0.94  cnf(c_0_63, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])]), ['proof']).
% 0.76/0.94  # SZS output end CNFRefutation
% 0.76/0.94  # Proof object total steps             : 64
% 0.76/0.94  # Proof object clause steps            : 41
% 0.76/0.94  # Proof object formula steps           : 23
% 0.76/0.94  # Proof object conjectures             : 21
% 0.76/0.94  # Proof object clause conjectures      : 18
% 0.76/0.94  # Proof object formula conjectures     : 3
% 0.76/0.94  # Proof object initial clauses used    : 15
% 0.76/0.94  # Proof object initial formulas used   : 11
% 0.76/0.94  # Proof object generating inferences   : 18
% 0.76/0.94  # Proof object simplifying inferences  : 20
% 0.76/0.94  # Training examples: 0 positive, 0 negative
% 0.76/0.94  # Parsed axioms                        : 12
% 0.76/0.94  # Removed by relevancy pruning/SinE    : 0
% 0.76/0.94  # Initial clauses                      : 25
% 0.76/0.94  # Removed in clause preprocessing      : 4
% 0.76/0.94  # Initial clauses in saturation        : 21
% 0.76/0.94  # Processed clauses                    : 2608
% 0.76/0.94  # ...of these trivial                  : 196
% 0.76/0.94  # ...subsumed                          : 1017
% 0.76/0.94  # ...remaining for further processing  : 1395
% 0.76/0.94  # Other redundant clauses eliminated   : 394
% 0.76/0.94  # Clauses deleted for lack of memory   : 0
% 0.76/0.94  # Backward-subsumed                    : 0
% 0.76/0.94  # Backward-rewritten                   : 38
% 0.76/0.94  # Generated clauses                    : 63433
% 0.76/0.94  # ...of the previous two non-trivial   : 60730
% 0.76/0.94  # Contextual simplify-reflections      : 0
% 0.76/0.94  # Paramodulations                      : 62876
% 0.76/0.94  # Factorizations                       : 158
% 0.76/0.94  # Equation resolutions                 : 399
% 0.76/0.94  # Propositional unsat checks           : 0
% 0.76/0.94  #    Propositional check models        : 0
% 0.76/0.94  #    Propositional check unsatisfiable : 0
% 0.76/0.94  #    Propositional clauses             : 0
% 0.76/0.94  #    Propositional clauses after purity: 0
% 0.76/0.94  #    Propositional unsat core size     : 0
% 0.76/0.94  #    Propositional preprocessing time  : 0.000
% 0.76/0.94  #    Propositional encoding time       : 0.000
% 0.76/0.94  #    Propositional solver time         : 0.000
% 0.76/0.94  #    Success case prop preproc time    : 0.000
% 0.76/0.94  #    Success case prop encoding time   : 0.000
% 0.76/0.94  #    Success case prop solver time     : 0.000
% 0.76/0.94  # Current number of processed clauses  : 1332
% 0.76/0.94  #    Positive orientable unit clauses  : 491
% 0.76/0.94  #    Positive unorientable unit clauses: 0
% 0.76/0.94  #    Negative unit clauses             : 0
% 0.76/0.94  #    Non-unit-clauses                  : 841
% 0.76/0.94  # Current number of unprocessed clauses: 58051
% 0.76/0.94  # ...number of literals in the above   : 129513
% 0.76/0.94  # Current number of archived formulas  : 0
% 0.76/0.94  # Current number of archived clauses   : 63
% 0.76/0.94  # Clause-clause subsumption calls (NU) : 70799
% 0.76/0.94  # Rec. Clause-clause subsumption calls : 65976
% 0.76/0.94  # Non-unit clause-clause subsumptions  : 1017
% 0.76/0.94  # Unit Clause-clause subsumption calls : 13697
% 0.76/0.94  # Rewrite failures with RHS unbound    : 0
% 0.76/0.94  # BW rewrite match attempts            : 21742
% 0.76/0.94  # BW rewrite match successes           : 38
% 0.76/0.94  # Condensation attempts                : 0
% 0.76/0.94  # Condensation successes               : 0
% 0.76/0.94  # Termbank termtop insertions          : 1808833
% 0.76/0.94  
% 0.76/0.94  # -------------------------------------------------
% 0.76/0.94  # User time                : 0.562 s
% 0.76/0.94  # System time              : 0.033 s
% 0.76/0.94  # Total time               : 0.595 s
% 0.76/0.94  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
