%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord1__t19_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:11 EDT 2019

% Result     : Theorem 0.82s
% Output     : CNFRefutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :  139 (1466 expanded)
%              Number of clauses        :   89 ( 649 expanded)
%              Number of leaves         :   25 ( 366 expanded)
%              Depth                    :   21
%              Number of atoms          :  327 (4510 expanded)
%              Number of equality atoms :   59 ( 823 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',d3_xboole_0)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',d6_relat_1)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',dt_k2_wellord1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',d4_xboole_0)).

fof(t119_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k8_relat_1(X1,X2)) = k3_xboole_0(k2_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',t119_relat_1)).

fof(t18_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,X1) = k8_relat_1(X1,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',t18_wellord1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',commutativity_k3_xboole_0)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',dt_k7_relat_1)).

fof(t19_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',t19_wellord1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',t90_relat_1)).

fof(t17_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,X1) = k7_relat_1(k8_relat_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',t17_wellord1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',dt_k8_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',t3_subset)).

fof(t99_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k7_relat_1(X2,X1)),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',t99_relat_1)).

fof(l29_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k8_relat_1(X1,X2)),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',l29_wellord1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',t4_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',t2_subset)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',t6_boole)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',existence_m1_subset_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',commutativity_k2_xboole_0)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',dt_o_0_0_xboole_0)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',t7_boole)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/wellord1__t19_wellord1.p',t2_boole)).

fof(c_0_25,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X17,X16)
        | r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X16 != k2_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X18,X14)
        | r2_hidden(X18,X16)
        | X16 != k2_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k2_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk4_3(X19,X20,X21),X19)
        | ~ r2_hidden(esk4_3(X19,X20,X21),X21)
        | X21 = k2_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk4_3(X19,X20,X21),X20)
        | ~ r2_hidden(esk4_3(X19,X20,X21),X21)
        | X21 = k2_xboole_0(X19,X20) )
      & ( r2_hidden(esk4_3(X19,X20,X21),X21)
        | r2_hidden(esk4_3(X19,X20,X21),X19)
        | r2_hidden(esk4_3(X19,X20,X21),X20)
        | X21 = k2_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_26,plain,(
    ! [X32] :
      ( ~ v1_relat_1(X32)
      | k3_relat_1(X32) = k2_xboole_0(k1_relat_1(X32),k2_relat_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_27,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X33)
      | v1_relat_1(k2_wellord1(X33,X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

fof(c_0_28,plain,(
    ! [X23,X24,X25,X26,X27,X28,X29,X30] :
      ( ( r2_hidden(X26,X23)
        | ~ r2_hidden(X26,X25)
        | X25 != k3_xboole_0(X23,X24) )
      & ( r2_hidden(X26,X24)
        | ~ r2_hidden(X26,X25)
        | X25 != k3_xboole_0(X23,X24) )
      & ( ~ r2_hidden(X27,X23)
        | ~ r2_hidden(X27,X24)
        | r2_hidden(X27,X25)
        | X25 != k3_xboole_0(X23,X24) )
      & ( ~ r2_hidden(esk5_3(X28,X29,X30),X30)
        | ~ r2_hidden(esk5_3(X28,X29,X30),X28)
        | ~ r2_hidden(esk5_3(X28,X29,X30),X29)
        | X30 = k3_xboole_0(X28,X29) )
      & ( r2_hidden(esk5_3(X28,X29,X30),X28)
        | r2_hidden(esk5_3(X28,X29,X30),X30)
        | X30 = k3_xboole_0(X28,X29) )
      & ( r2_hidden(esk5_3(X28,X29,X30),X29)
        | r2_hidden(esk5_3(X28,X29,X30),X30)
        | X30 = k3_xboole_0(X28,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_29,plain,(
    ! [X45,X46] :
      ( ~ v1_relat_1(X46)
      | k2_relat_1(k8_relat_1(X45,X46)) = k3_xboole_0(k2_relat_1(X46),X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_relat_1])])).

fof(c_0_30,plain,(
    ! [X49,X50] :
      ( ~ v1_relat_1(X50)
      | k2_wellord1(X50,X49) = k8_relat_1(X49,k7_relat_1(X50,X49)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_wellord1])])).

fof(c_0_31,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k3_xboole_0(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_32,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X35)
      | v1_relat_1(k7_relat_1(X35,X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))
         => ( r2_hidden(X1,k3_relat_1(X3))
            & r2_hidden(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t19_wellord1])).

fof(c_0_37,plain,(
    ! [X70,X71] :
      ( ~ v1_relat_1(X71)
      | k1_relat_1(k7_relat_1(X71,X70)) = k3_xboole_0(k1_relat_1(X71),X70) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_38,plain,(
    ! [X47,X48] :
      ( ~ v1_relat_1(X48)
      | k2_wellord1(X48,X47) = k7_relat_1(k8_relat_1(X47,X48),X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_wellord1])])).

fof(c_0_39,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X38)
      | v1_relat_1(k8_relat_1(X37,X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( k2_relat_1(k8_relat_1(X2,X1)) = k3_xboole_0(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( k2_wellord1(X1,X2) = k8_relat_1(X2,k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k2_xboole_0(k1_relat_1(k2_wellord1(X1,X2)),k2_relat_1(k2_wellord1(X1,X2))) = k3_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_47,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r2_hidden(esk1_0,k3_relat_1(k2_wellord1(esk3_0,esk2_0)))
    & ( ~ r2_hidden(esk1_0,k3_relat_1(esk3_0))
      | ~ r2_hidden(esk1_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).

fof(c_0_48,plain,(
    ! [X57,X58] :
      ( ( ~ m1_subset_1(X57,k1_zfmisc_1(X58))
        | r1_tarski(X57,X58) )
      & ( ~ r1_tarski(X57,X58)
        | m1_subset_1(X57,k1_zfmisc_1(X58)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_49,plain,(
    ! [X72,X73] :
      ( ~ v1_relat_1(X73)
      | r1_tarski(k2_relat_1(k7_relat_1(X73,X72)),k2_relat_1(X73)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t99_relat_1])])).

cnf(c_0_50,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,plain,
    ( k2_wellord1(X1,X2) = k7_relat_1(k8_relat_1(X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,k2_relat_1(k7_relat_1(X2,X1))) = k2_relat_1(k2_wellord1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k2_relat_1(k2_wellord1(X2,X3)))
    | r2_hidden(X1,k1_relat_1(k2_wellord1(X2,X3)))
    | ~ r2_hidden(X1,k3_relat_1(k2_wellord1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk1_0,k3_relat_1(k2_wellord1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_58,plain,(
    ! [X43,X44] :
      ( ~ v1_relat_1(X44)
      | r1_tarski(k1_relat_1(k8_relat_1(X43,X44)),k1_relat_1(X44)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l29_wellord1])])).

fof(c_0_59,plain,(
    ! [X59,X60,X61] :
      ( ~ r2_hidden(X59,X60)
      | ~ m1_subset_1(X60,k1_zfmisc_1(X61))
      | m1_subset_1(X59,X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,k1_relat_1(k8_relat_1(X1,X2))) = k1_relat_1(k2_wellord1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_43]),c_0_52])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,k2_relat_1(k7_relat_1(X2,X3)))
    | ~ r2_hidden(X1,k2_relat_1(k2_wellord1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(k2_wellord1(esk3_0,esk2_0)))
    | r2_hidden(esk1_0,k2_relat_1(k2_wellord1(esk3_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X2,X1)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,plain,
    ( m1_subset_1(k2_relat_1(k7_relat_1(X1,X2)),k1_zfmisc_1(k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
    | ~ r2_hidden(X1,k1_relat_1(k2_wellord1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_53,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(k2_wellord1(esk3_0,esk2_0)))
    | r2_hidden(esk1_0,k2_relat_1(k7_relat_1(esk3_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_57])])).

fof(c_0_70,plain,(
    ! [X62,X63,X64] :
      ( ~ r2_hidden(X62,X63)
      | ~ m1_subset_1(X63,k1_zfmisc_1(X64))
      | ~ v1_xboole_0(X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_71,plain,
    ( m1_subset_1(k1_relat_1(k8_relat_1(X1,X2)),k1_zfmisc_1(k1_relat_1(X2)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_65])).

cnf(c_0_72,plain,
    ( m1_subset_1(X1,k2_relat_1(X2))
    | ~ r2_hidden(X1,k2_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk1_0,k2_relat_1(k7_relat_1(esk3_0,esk2_0)))
    | r2_hidden(esk1_0,k1_relat_1(k8_relat_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_57])])).

cnf(c_0_74,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_75,plain,(
    ! [X55,X56] :
      ( ~ m1_subset_1(X55,X56)
      | v1_xboole_0(X56)
      | r2_hidden(X55,X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_76,plain,
    ( m1_subset_1(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k8_relat_1(X3,X2)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk1_0,k2_relat_1(esk3_0))
    | r2_hidden(esk1_0,k1_relat_1(k8_relat_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_57])])).

cnf(c_0_78,plain,
    ( ~ v1_xboole_0(k2_relat_1(X1))
    | ~ r2_hidden(X2,k2_relat_1(k7_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_67])).

cnf(c_0_79,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk1_0,k2_relat_1(esk3_0))
    | m1_subset_1(esk1_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_57])])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(k8_relat_1(esk2_0,esk3_0)))
    | ~ v1_xboole_0(k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_73]),c_0_57])])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk1_0,k1_relat_1(esk3_0))
    | v1_xboole_0(k2_relat_1(esk3_0))
    | r2_hidden(esk1_0,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(esk1_0,k1_relat_1(esk3_0))
    | r2_hidden(esk1_0,k1_relat_1(k8_relat_1(esk2_0,esk3_0)))
    | r2_hidden(esk1_0,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_relat_1(k2_wellord1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_84,c_0_54])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_88,plain,(
    ! [X65] :
      ( ~ v1_xboole_0(X65)
      | X65 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk1_0,k1_relat_1(esk3_0))
    | r2_hidden(esk1_0,k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_85]),c_0_57])])).

cnf(c_0_90,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k2_wellord1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_84,c_0_62])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(k2_wellord1(esk3_0,esk2_0)))
    | r2_hidden(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_64]),c_0_57])])).

cnf(c_0_92,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_93,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(esk3_0),k2_relat_1(esk3_0)) = k3_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_57])).

cnf(c_0_95,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_96,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk3_0))
    | r2_hidden(esk1_0,k2_relat_1(esk3_0))
    | r2_hidden(esk1_0,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_89])).

cnf(c_0_97,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k3_relat_1(esk3_0))
    | ~ r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_57])])).

fof(c_0_99,plain,(
    ! [X39] : m1_subset_1(esk6_1(X39),X39) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_100,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_92])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk3_0))
    | ~ r2_hidden(X1,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_102,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_xboole_0
    | r2_hidden(esk1_0,k1_relat_1(esk3_0))
    | r2_hidden(esk1_0,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_103,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k3_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_98])])).

fof(c_0_104,plain,(
    ! [X51] : k2_xboole_0(X51,k1_xboole_0) = X51 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_105,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k2_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_106,plain,
    ( m1_subset_1(k2_relat_1(k2_wellord1(X1,X2)),k1_zfmisc_1(k2_relat_1(k8_relat_1(X2,X1))))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_51]),c_0_52])).

cnf(c_0_107,plain,
    ( m1_subset_1(esk6_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_108,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk3_0))
    | ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_94])).

cnf(c_0_110,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_xboole_0
    | r2_hidden(esk1_0,k1_relat_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_103])).

cnf(c_0_111,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_112,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_113,plain,
    ( ~ v1_xboole_0(k2_relat_1(k8_relat_1(X1,X2)))
    | ~ r2_hidden(X3,k2_relat_1(k2_wellord1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_106])).

fof(c_0_114,plain,(
    ! [X66,X67] :
      ( ~ r2_hidden(X66,X67)
      | ~ v1_xboole_0(X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_115,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk6_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_107])).

cnf(c_0_116,plain,
    ( ~ v1_xboole_0(k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(k8_relat_1(X3,X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_71])).

cnf(c_0_117,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_95,c_0_108])).

cnf(c_0_118,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_103])).

cnf(c_0_119,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_120,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(k2_wellord1(esk3_0,esk2_0)))
    | ~ v1_xboole_0(k2_relat_1(k8_relat_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_64]),c_0_57])])).

cnf(c_0_121,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_114])).

cnf(c_0_122,plain,
    ( v1_xboole_0(k3_xboole_0(X1,X2))
    | r2_hidden(esk6_1(k3_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_115])).

cnf(c_0_123,negated_conjecture,
    ( m1_subset_1(esk1_0,k2_relat_1(esk3_0))
    | ~ v1_xboole_0(k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_77]),c_0_57])])).

cnf(c_0_124,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_108,c_0_117])).

cnf(c_0_125,negated_conjecture,
    ( k3_relat_1(esk3_0) = k2_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_118]),c_0_119])).

cnf(c_0_126,plain,
    ( m1_subset_1(k1_relat_1(k8_relat_1(X1,k7_relat_1(X2,X3))),k1_zfmisc_1(k3_xboole_0(k1_relat_1(X2),X3)))
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_50]),c_0_44])).

cnf(c_0_127,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(k2_wellord1(esk3_0,esk2_0)))
    | ~ v1_xboole_0(k3_xboole_0(esk2_0,k2_relat_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_41]),c_0_43]),c_0_57])])).

cnf(c_0_128,plain,
    ( v1_xboole_0(k3_xboole_0(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_129,negated_conjecture,
    ( m1_subset_1(esk1_0,k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123,c_0_118]),c_0_124])])).

cnf(c_0_130,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k2_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_103,c_0_125])).

cnf(c_0_131,plain,
    ( ~ v1_xboole_0(k3_xboole_0(k1_relat_1(X1),X2))
    | ~ r2_hidden(X3,k1_relat_1(k8_relat_1(X4,k7_relat_1(X1,X2))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_126])).

cnf(c_0_132,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(k2_wellord1(esk3_0,esk2_0)))
    | ~ v1_xboole_0(k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_133,negated_conjecture,
    ( v1_xboole_0(k2_relat_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_129]),c_0_130])).

fof(c_0_134,plain,(
    ! [X54] : k3_xboole_0(X54,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_135,plain,
    ( ~ v1_xboole_0(k3_xboole_0(k1_relat_1(X1),X2))
    | ~ r2_hidden(X3,k1_relat_1(k2_wellord1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_131,c_0_42])).

cnf(c_0_136,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(k2_wellord1(esk3_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_132,c_0_133])])).

cnf(c_0_137,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_134])).

cnf(c_0_138,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_43]),c_0_118]),c_0_137]),c_0_124]),c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
