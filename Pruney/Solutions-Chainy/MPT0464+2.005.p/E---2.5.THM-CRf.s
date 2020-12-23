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
% DateTime   : Thu Dec  3 10:48:38 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 266 expanded)
%              Number of clauses        :   33 ( 111 expanded)
%              Number of leaves         :   13 (  75 expanded)
%              Depth                    :   12
%              Number of atoms          :  125 ( 412 expanded)
%              Number of equality atoms :   25 ( 194 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(t52_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_13,plain,(
    ! [X29,X30] : k1_setfam_1(k2_tarski(X29,X30)) = k3_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_14,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X10,X11] : r1_tarski(k3_xboole_0(X10,X11),X10) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_16,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X20,X21,X22,X23] : k3_enumset1(X20,X20,X21,X22,X23) = k2_enumset1(X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_20,plain,(
    ! [X24,X25,X26,X27,X28] : k4_enumset1(X24,X24,X25,X26,X27,X28) = k3_enumset1(X24,X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_21,plain,(
    ! [X31,X32] :
      ( ( ~ m1_subset_1(X31,k1_zfmisc_1(X32))
        | r1_tarski(X31,X32) )
      & ( ~ r1_tarski(X31,X32)
        | m1_subset_1(X31,k1_zfmisc_1(X32)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_22,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(X33))
      | v1_relat_1(X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_26])).

fof(c_0_30,plain,(
    ! [X35,X36,X37,X38] :
      ( ~ v1_relat_1(X35)
      | ~ v1_relat_1(X36)
      | ~ v1_relat_1(X37)
      | ~ v1_relat_1(X38)
      | ~ r1_tarski(X35,X36)
      | ~ r1_tarski(X37,X38)
      | r1_tarski(k5_relat_1(X35,X37),k5_relat_1(X36,X38)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_relat_1])])])).

cnf(c_0_31,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( m1_subset_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_33,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_34,plain,
    ( r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( v1_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_37,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relat_1])).

cnf(c_0_38,plain,
    ( r1_tarski(k5_relat_1(X1,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3))),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_29]),c_0_35])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_36])).

fof(c_0_40,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).

fof(c_0_41,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_tarski(X12,X14)
      | r1_tarski(X12,k3_xboole_0(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_42,plain,
    ( r1_tarski(k5_relat_1(X1,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3))),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_45,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X2))),k5_relat_1(X1,esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,k1_setfam_1(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X2))),k5_relat_1(X1,esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_44])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_23]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))),k5_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1))),k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_48])).

cnf(c_0_54,plain,
    ( k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)) = k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_26]),c_0_26])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))),k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,k5_relat_1(esk1_0,esk3_0))))
    | ~ r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))),X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,esk2_0))),k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))),k1_setfam_1(k4_enumset1(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_26]),c_0_26])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_54]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:54:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.47  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S064A
% 0.20/0.47  # and selection function SelectComplexG.
% 0.20/0.47  #
% 0.20/0.47  # Preprocessing time       : 0.027 s
% 0.20/0.47  # Presaturation interreduction done
% 0.20/0.47  
% 0.20/0.47  # Proof found!
% 0.20/0.47  # SZS status Theorem
% 0.20/0.47  # SZS output start CNFRefutation
% 0.20/0.47  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.47  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.47  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.47  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.47  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.47  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.47  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.47  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.47  fof(t50_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relat_1)).
% 0.20/0.47  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.47  fof(t52_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 0.20/0.47  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.20/0.47  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.47  fof(c_0_13, plain, ![X29, X30]:k1_setfam_1(k2_tarski(X29,X30))=k3_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.47  fof(c_0_14, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.47  fof(c_0_15, plain, ![X10, X11]:r1_tarski(k3_xboole_0(X10,X11),X10), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.47  cnf(c_0_16, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.47  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.47  fof(c_0_18, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.47  fof(c_0_19, plain, ![X20, X21, X22, X23]:k3_enumset1(X20,X20,X21,X22,X23)=k2_enumset1(X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.47  fof(c_0_20, plain, ![X24, X25, X26, X27, X28]:k4_enumset1(X24,X24,X25,X26,X27,X28)=k3_enumset1(X24,X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.47  fof(c_0_21, plain, ![X31, X32]:((~m1_subset_1(X31,k1_zfmisc_1(X32))|r1_tarski(X31,X32))&(~r1_tarski(X31,X32)|m1_subset_1(X31,k1_zfmisc_1(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.47  cnf(c_0_22, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.47  cnf(c_0_23, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.47  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.47  cnf(c_0_25, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.47  cnf(c_0_26, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.47  fof(c_0_27, plain, ![X33, X34]:(~v1_relat_1(X33)|(~m1_subset_1(X34,k1_zfmisc_1(X33))|v1_relat_1(X34))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.47  cnf(c_0_28, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.47  cnf(c_0_29, plain, (r1_tarski(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 0.20/0.47  fof(c_0_30, plain, ![X35, X36, X37, X38]:(~v1_relat_1(X35)|(~v1_relat_1(X36)|(~v1_relat_1(X37)|(~v1_relat_1(X38)|(~r1_tarski(X35,X36)|~r1_tarski(X37,X38)|r1_tarski(k5_relat_1(X35,X37),k5_relat_1(X36,X38))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_relat_1])])])).
% 0.20/0.47  cnf(c_0_31, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.47  cnf(c_0_32, plain, (m1_subset_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.47  fof(c_0_33, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.47  cnf(c_0_34, plain, (r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~v1_relat_1(X4)|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.47  cnf(c_0_35, plain, (v1_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.47  cnf(c_0_36, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.47  fof(c_0_37, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t52_relat_1])).
% 0.20/0.47  cnf(c_0_38, plain, (r1_tarski(k5_relat_1(X1,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3))),k5_relat_1(X4,X2))|~v1_relat_1(X2)|~v1_relat_1(X4)|~v1_relat_1(X1)|~r1_tarski(X1,X4)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_29]), c_0_35])).
% 0.20/0.47  cnf(c_0_39, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_36])).
% 0.20/0.47  fof(c_0_40, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).
% 0.20/0.47  fof(c_0_41, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_tarski(X12,X14)|r1_tarski(X12,k3_xboole_0(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.20/0.47  cnf(c_0_42, plain, (r1_tarski(k5_relat_1(X1,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3))),k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.47  cnf(c_0_43, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.47  cnf(c_0_44, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.47  fof(c_0_45, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.47  cnf(c_0_46, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.47  cnf(c_0_47, negated_conjecture, (r1_tarski(k5_relat_1(X1,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X2))),k5_relat_1(X1,esk3_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.47  cnf(c_0_48, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.47  cnf(c_0_49, negated_conjecture, (r1_tarski(k5_relat_1(X1,k1_setfam_1(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X2))),k5_relat_1(X1,esk2_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_44])).
% 0.20/0.47  cnf(c_0_50, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.47  cnf(c_0_51, plain, (r1_tarski(X1,k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 0.20/0.47  cnf(c_0_52, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))),k5_relat_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.47  cnf(c_0_53, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,X1))),k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_49, c_0_48])).
% 0.20/0.47  cnf(c_0_54, plain, (k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))=k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_26]), c_0_26])).
% 0.20/0.47  cnf(c_0_55, negated_conjecture, (~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.47  cnf(c_0_56, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))),k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,k5_relat_1(esk1_0,esk3_0))))|~r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))),X2)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.47  cnf(c_0_57, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,esk2_0))),k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.47  cnf(c_0_58, negated_conjecture, (~r1_tarski(k5_relat_1(esk1_0,k1_setfam_1(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0))),k1_setfam_1(k4_enumset1(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_26]), c_0_26])).
% 0.20/0.47  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_54]), c_0_58]), ['proof']).
% 0.20/0.47  # SZS output end CNFRefutation
% 0.20/0.47  # Proof object total steps             : 60
% 0.20/0.47  # Proof object clause steps            : 33
% 0.20/0.47  # Proof object formula steps           : 27
% 0.20/0.47  # Proof object conjectures             : 15
% 0.20/0.47  # Proof object clause conjectures      : 12
% 0.20/0.47  # Proof object formula conjectures     : 3
% 0.20/0.47  # Proof object initial clauses used    : 16
% 0.20/0.47  # Proof object initial formulas used   : 13
% 0.20/0.47  # Proof object generating inferences   : 11
% 0.20/0.47  # Proof object simplifying inferences  : 29
% 0.20/0.47  # Training examples: 0 positive, 0 negative
% 0.20/0.47  # Parsed axioms                        : 13
% 0.20/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.47  # Initial clauses                      : 19
% 0.20/0.47  # Removed in clause preprocessing      : 5
% 0.20/0.47  # Initial clauses in saturation        : 14
% 0.20/0.47  # Processed clauses                    : 745
% 0.20/0.47  # ...of these trivial                  : 189
% 0.20/0.47  # ...subsumed                          : 125
% 0.20/0.47  # ...remaining for further processing  : 431
% 0.20/0.47  # Other redundant clauses eliminated   : 2
% 0.20/0.47  # Clauses deleted for lack of memory   : 0
% 0.20/0.47  # Backward-subsumed                    : 0
% 0.20/0.47  # Backward-rewritten                   : 3
% 0.20/0.47  # Generated clauses                    : 5008
% 0.20/0.47  # ...of the previous two non-trivial   : 3711
% 0.20/0.47  # Contextual simplify-reflections      : 42
% 0.20/0.47  # Paramodulations                      : 5006
% 0.20/0.47  # Factorizations                       : 0
% 0.20/0.47  # Equation resolutions                 : 2
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
% 0.20/0.47  # Current number of processed clauses  : 413
% 0.20/0.47  #    Positive orientable unit clauses  : 209
% 0.20/0.47  #    Positive unorientable unit clauses: 1
% 0.20/0.47  #    Negative unit clauses             : 1
% 0.20/0.47  #    Non-unit-clauses                  : 202
% 0.20/0.47  # Current number of unprocessed clauses: 2979
% 0.20/0.47  # ...number of literals in the above   : 4751
% 0.20/0.47  # Current number of archived formulas  : 0
% 0.20/0.47  # Current number of archived clauses   : 21
% 0.20/0.47  # Clause-clause subsumption calls (NU) : 10170
% 0.20/0.47  # Rec. Clause-clause subsumption calls : 4627
% 0.20/0.47  # Non-unit clause-clause subsumptions  : 166
% 0.20/0.47  # Unit Clause-clause subsumption calls : 3170
% 0.20/0.47  # Rewrite failures with RHS unbound    : 0
% 0.20/0.47  # BW rewrite match attempts            : 1088
% 0.20/0.47  # BW rewrite match successes           : 11
% 0.20/0.47  # Condensation attempts                : 0
% 0.20/0.47  # Condensation successes               : 0
% 0.20/0.47  # Termbank termtop insertions          : 211858
% 0.20/0.47  
% 0.20/0.47  # -------------------------------------------------
% 0.20/0.47  # User time                : 0.120 s
% 0.20/0.47  # System time              : 0.009 s
% 0.20/0.47  # Total time               : 0.128 s
% 0.20/0.47  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
