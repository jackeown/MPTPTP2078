%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1003+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:00 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 358 expanded)
%              Number of clauses        :   40 ( 142 expanded)
%              Number of leaves         :   16 (  87 expanded)
%              Depth                    :   11
%              Number of atoms          :  210 (1319 expanded)
%              Number of equality atoms :   82 ( 644 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => k8_relset_1(X1,X2,X3,k7_relset_1(X1,X2,X3,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',cc2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',fc6_relat_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',redefinition_k2_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',d19_relat_1)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',t38_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',redefinition_k1_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT006+2.ax',t3_subset)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(t39_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
     => ( k7_relset_1(X2,X1,X3,k8_relset_1(X2,X1,X3,X1)) = k2_relset_1(X2,X1,X3)
        & k8_relset_1(X2,X1,X3,k7_relset_1(X2,X1,X3,X2)) = k1_relset_1(X2,X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',t39_relset_1)).

fof(t67_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X2,X3) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t67_xboole_1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t113_zfmisc_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t65_xboole_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t60_relat_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => k8_relset_1(X1,X2,X3,k7_relset_1(X1,X2,X3,X1)) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t51_funct_2])).

fof(c_0_17,plain,(
    ! [X3654,X3655,X3656] :
      ( ( v4_relat_1(X3656,X3654)
        | ~ m1_subset_1(X3656,k1_zfmisc_1(k2_zfmisc_1(X3654,X3655))) )
      & ( v5_relat_1(X3656,X3655)
        | ~ m1_subset_1(X3656,k1_zfmisc_1(k2_zfmisc_1(X3654,X3655))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_18,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & ( esk2_0 != k1_xboole_0
      | esk1_0 = k1_xboole_0 )
    & k8_relset_1(esk1_0,esk2_0,esk3_0,k7_relset_1(esk1_0,esk2_0,esk3_0,esk1_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_19,plain,(
    ! [X381,X382] :
      ( ~ v1_relat_1(X381)
      | ~ m1_subset_1(X382,k1_zfmisc_1(X381))
      | v1_relat_1(X382) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_20,plain,(
    ! [X624,X625] : v1_relat_1(k2_zfmisc_1(X624,X625)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_21,plain,(
    ! [X1173,X1174,X1175] :
      ( ~ m1_subset_1(X1175,k1_zfmisc_1(k2_zfmisc_1(X1173,X1174)))
      | k2_relset_1(X1173,X1174,X1175) = k2_relat_1(X1175) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_22,plain,(
    ! [X2999,X3000] :
      ( ( ~ v5_relat_1(X3000,X2999)
        | r1_tarski(k2_relat_1(X3000),X2999)
        | ~ v1_relat_1(X3000) )
      & ( ~ r1_tarski(k2_relat_1(X3000),X2999)
        | v5_relat_1(X3000,X2999)
        | ~ v1_relat_1(X3000) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_23,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X24,X25,X26] :
      ( ( k7_relset_1(X24,X25,X26,X24) = k2_relset_1(X24,X25,X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( k8_relset_1(X24,X25,X26,X25) = k1_relset_1(X24,X25,X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

cnf(c_0_28,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X1133,X1134,X1135] :
      ( ~ m1_subset_1(X1135,k1_zfmisc_1(k2_zfmisc_1(X1133,X1134)))
      | k1_relset_1(X1133,X1134,X1135) = k1_relat_1(X1135) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_30,plain,(
    ! [X369,X370] :
      ( ( ~ m1_subset_1(X369,k1_zfmisc_1(X370))
        | r1_tarski(X369,X370) )
      & ( ~ r1_tarski(X369,X370)
        | m1_subset_1(X369,k1_zfmisc_1(X370)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_31,plain,(
    ! [X464,X465] :
      ( ( v1_funct_1(X465)
        | ~ r1_tarski(k2_relat_1(X465),X464)
        | ~ v1_relat_1(X465)
        | ~ v1_funct_1(X465) )
      & ( v1_funct_2(X465,k1_relat_1(X465),X464)
        | ~ r1_tarski(k2_relat_1(X465),X464)
        | ~ v1_relat_1(X465)
        | ~ v1_funct_1(X465) )
      & ( m1_subset_1(X465,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X465),X464)))
        | ~ r1_tarski(k2_relat_1(X465),X464)
        | ~ v1_relat_1(X465)
        | ~ v1_funct_1(X465) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

cnf(c_0_32,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( v5_relat_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_24]),c_0_26])])).

cnf(c_0_35,plain,
    ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = k2_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_24])).

fof(c_0_37,plain,(
    ! [X27,X28,X29] :
      ( ( k7_relset_1(X28,X27,X29,k8_relset_1(X28,X27,X29,X27)) = k2_relset_1(X28,X27,X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X28,X27))) )
      & ( k8_relset_1(X28,X27,X29,k7_relset_1(X28,X27,X29,X28)) = k1_relset_1(X28,X27,X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X28,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_relset_1])])])).

cnf(c_0_38,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_39,plain,(
    ! [X109,X110,X111] :
      ( ~ r1_tarski(X109,X110)
      | ~ r1_tarski(X109,X111)
      | ~ r1_xboole_0(X110,X111)
      | X109 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_44,plain,(
    ! [X658,X659,X660] :
      ( ( ~ v1_funct_2(X660,X658,X659)
        | X658 = k1_relset_1(X658,X659,X660)
        | X659 = k1_xboole_0
        | ~ m1_subset_1(X660,k1_zfmisc_1(k2_zfmisc_1(X658,X659))) )
      & ( X658 != k1_relset_1(X658,X659,X660)
        | v1_funct_2(X660,X658,X659)
        | X659 = k1_xboole_0
        | ~ m1_subset_1(X660,k1_zfmisc_1(k2_zfmisc_1(X658,X659))) )
      & ( ~ v1_funct_2(X660,X658,X659)
        | X658 = k1_relset_1(X658,X659,X660)
        | X658 != k1_xboole_0
        | ~ m1_subset_1(X660,k1_zfmisc_1(k2_zfmisc_1(X658,X659))) )
      & ( X658 != k1_relset_1(X658,X659,X660)
        | v1_funct_2(X660,X658,X659)
        | X658 != k1_xboole_0
        | ~ m1_subset_1(X660,k1_zfmisc_1(k2_zfmisc_1(X658,X659))) )
      & ( ~ v1_funct_2(X660,X658,X659)
        | X660 = k1_xboole_0
        | X658 = k1_xboole_0
        | X659 != k1_xboole_0
        | ~ m1_subset_1(X660,k1_zfmisc_1(k2_zfmisc_1(X658,X659))) )
      & ( X660 != k1_xboole_0
        | v1_funct_2(X660,X658,X659)
        | X658 = k1_xboole_0
        | X659 != k1_xboole_0
        | ~ m1_subset_1(X660,k1_zfmisc_1(k2_zfmisc_1(X658,X659))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_45,negated_conjecture,
    ( k8_relset_1(esk1_0,esk2_0,esk3_0,k7_relset_1(esk1_0,esk2_0,esk3_0,esk1_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_46,negated_conjecture,
    ( k7_relset_1(esk1_0,esk2_0,esk3_0,esk1_0) = k2_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_24]),c_0_36])).

cnf(c_0_47,plain,
    ( k8_relset_1(X1,X2,X3,k7_relset_1(X1,X2,X3,X1)) = k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk3_0) = k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_24])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk3_0,k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_24])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk3_0),esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_34])])).

cnf(c_0_52,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_54,negated_conjecture,
    ( k8_relset_1(esk1_0,esk2_0,esk3_0,k2_relat_1(esk3_0)) != esk1_0 ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( k8_relset_1(esk1_0,esk2_0,esk3_0,k2_relat_1(esk3_0)) = k1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_24]),c_0_46]),c_0_48])).

fof(c_0_56,plain,(
    ! [X123,X124] :
      ( ( k2_zfmisc_1(X123,X124) != k1_xboole_0
        | X123 = k1_xboole_0
        | X124 = k1_xboole_0 )
      & ( X123 != k1_xboole_0
        | k2_zfmisc_1(X123,X124) = k1_xboole_0 )
      & ( X124 != k1_xboole_0
        | k2_zfmisc_1(X123,X124) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_57,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r1_xboole_0(X1,k2_zfmisc_1(esk1_0,esk2_0))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk3_0,k2_zfmisc_1(k1_relat_1(esk3_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_48]),c_0_24])])).

cnf(c_0_60,negated_conjecture,
    ( k1_relat_1(esk3_0) != esk1_0 ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_62,plain,(
    ! [X107] : r1_xboole_0(X107,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_63,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r1_xboole_0(k2_zfmisc_1(k1_relat_1(esk3_0),esk2_0),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_66,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_64]),c_0_65]),c_0_66])])).

cnf(c_0_68,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_69,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_70,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_67]),c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_64])]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
