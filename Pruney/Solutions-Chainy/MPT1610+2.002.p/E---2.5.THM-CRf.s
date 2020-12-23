%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:49 EST 2020

% Result     : Theorem 10.45s
% Output     : CNFRefutation 10.45s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 170 expanded)
%              Number of clauses        :   44 (  77 expanded)
%              Number of leaves         :   20 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  154 ( 370 expanded)
%              Number of equality atoms :   98 ( 246 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   16 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t18_funct_1,axiom,(
    ! [X1,X2] :
      ~ ( ~ ( X1 = k1_xboole_0
            & X2 != k1_xboole_0 )
        & ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ~ ( X2 = k1_relat_1(X3)
                & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t18_yellow_1,conjecture,(
    ! [X1] : k3_yellow_0(k3_yellow_1(X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t93_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(t4_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t52_ordinal1,axiom,(
    ! [X1] : k6_subset_1(k1_ordinal1(X1),k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_ordinal1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t13_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k1_xboole_0,X1)
       => k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(c_0_20,plain,(
    ! [X32,X33] : k1_setfam_1(k2_tarski(X32,X33)) = k3_xboole_0(X32,X33) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_21,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X35,X36] :
      ( ( v1_relat_1(esk2_2(X35,X36))
        | X35 = k1_xboole_0 )
      & ( v1_funct_1(esk2_2(X35,X36))
        | X35 = k1_xboole_0 )
      & ( X36 = k1_relat_1(esk2_2(X35,X36))
        | X35 = k1_xboole_0 )
      & ( r1_tarski(k2_relat_1(esk2_2(X35,X36)),X35)
        | X35 = k1_xboole_0 )
      & ( v1_relat_1(esk2_2(X35,X36))
        | X36 != k1_xboole_0 )
      & ( v1_funct_1(esk2_2(X35,X36))
        | X36 != k1_xboole_0 )
      & ( X36 = k1_relat_1(esk2_2(X35,X36))
        | X36 != k1_xboole_0 )
      & ( r1_tarski(k2_relat_1(esk2_2(X35,X36)),X35)
        | X36 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_funct_1])])])])).

fof(c_0_23,plain,(
    ! [X7,X8] : k4_xboole_0(X7,X8) = k5_xboole_0(X7,k3_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1] : k3_yellow_0(k3_yellow_1(X1)) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t18_yellow_1])).

fof(c_0_27,plain,(
    ! [X34] :
      ( ( k1_relat_1(X34) != k1_xboole_0
        | X34 = k1_xboole_0
        | ~ v1_relat_1(X34) )
      & ( k2_relat_1(X34) != k1_xboole_0
        | X34 = k1_xboole_0
        | ~ v1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_28,plain,
    ( v1_relat_1(esk2_2(X1,X2))
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( X1 = k1_relat_1(esk2_2(X2,X1))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X24,X25,X26] :
      ( ( r2_hidden(X24,X25)
        | ~ r2_hidden(X24,k4_xboole_0(X25,k1_tarski(X26))) )
      & ( X24 != X26
        | ~ r2_hidden(X24,k4_xboole_0(X25,k1_tarski(X26))) )
      & ( ~ r2_hidden(X24,X25)
        | X24 = X26
        | r2_hidden(X24,k4_xboole_0(X25,k1_tarski(X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_31,plain,(
    ! [X11] : k2_tarski(X11,X11) = k1_tarski(X11) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_34,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_35,plain,(
    ! [X38] : k1_ordinal1(X38) = k2_xboole_0(X38,k1_tarski(X38)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_36,plain,(
    ! [X27,X28] : k3_tarski(k2_tarski(X27,X28)) = k2_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t93_zfmisc_1])).

fof(c_0_37,negated_conjecture,(
    k3_yellow_0(k3_yellow_1(esk3_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

fof(c_0_38,plain,(
    ! [X42] : k3_yellow_1(X42) = k3_lattice3(k1_lattice3(X42)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_39,plain,(
    ! [X44] : k3_yellow_1(X44) = k2_yellow_1(k9_setfam_1(X44)) ),
    inference(variable_rename,[status(thm)],[t4_yellow_1])).

fof(c_0_40,plain,(
    ! [X41] : k9_setfam_1(X41) = k1_zfmisc_1(X41) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_41,plain,(
    ! [X17,X18,X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X19,X18)
        | r1_tarski(X19,X17)
        | X18 != k1_zfmisc_1(X17) )
      & ( ~ r1_tarski(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k1_zfmisc_1(X17) )
      & ( ~ r2_hidden(esk1_2(X21,X22),X22)
        | ~ r1_tarski(esk1_2(X21,X22),X21)
        | X22 = k1_zfmisc_1(X21) )
      & ( r2_hidden(esk1_2(X21,X22),X22)
        | r1_tarski(esk1_2(X21,X22),X21)
        | X22 = k1_zfmisc_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_42,plain,
    ( r1_tarski(k2_relat_1(esk2_2(X1,X2)),X1)
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_44,plain,
    ( v1_relat_1(esk2_2(X1,k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_45,plain,
    ( k1_relat_1(esk2_2(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_46,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_47,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_49,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_50,plain,(
    ! [X40] : k6_subset_1(k1_ordinal1(X40),k1_tarski(X40)) = X40 ),
    inference(variable_rename,[status(thm)],[t52_ordinal1])).

fof(c_0_51,plain,(
    ! [X30,X31] : k6_subset_1(X30,X31) = k4_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_52,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_53,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_54,negated_conjecture,
    ( k3_yellow_0(k3_yellow_1(esk3_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_55,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_56,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_57,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_58,plain,(
    ! [X43] :
      ( v1_xboole_0(X43)
      | ~ r2_hidden(k1_xboole_0,X43)
      | k3_yellow_0(k2_yellow_1(X43)) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t13_yellow_1])])])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_60,plain,
    ( r1_tarski(k2_relat_1(esk2_2(X1,k1_xboole_0)),X1) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_61,plain,
    ( esk2_2(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_62,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_63,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k5_xboole_0(X3,k1_setfam_1(k2_enumset1(X3,X3,X3,k2_enumset1(X2,X2,X2,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_25]),c_0_48]),c_0_49]),c_0_49])).

cnf(c_0_64,plain,
    ( k6_subset_1(k1_ordinal1(X1),k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_65,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_66,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_52,c_0_47])).

cnf(c_0_67,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_53,c_0_25])).

cnf(c_0_68,negated_conjecture,
    ( k3_yellow_0(k3_lattice3(k1_lattice3(esk3_0))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_69,plain,
    ( k2_yellow_1(k1_zfmisc_1(X1)) = k3_lattice3(k1_lattice3(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57]),c_0_55])).

cnf(c_0_70,plain,
    ( v1_xboole_0(X1)
    | k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_72,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_enumset1(X2,X2,X2,k2_enumset1(X1,X1,X1,X1))))) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_74,plain,
    ( k5_xboole_0(k3_tarski(k2_enumset1(X1,X1,X1,k2_enumset1(X1,X1,X1,X1))),k1_setfam_1(k2_enumset1(k3_tarski(k2_enumset1(X1,X1,X1,k2_enumset1(X1,X1,X1,X1))),k3_tarski(k2_enumset1(X1,X1,X1,k2_enumset1(X1,X1,X1,X1))),k3_tarski(k2_enumset1(X1,X1,X1,k2_enumset1(X1,X1,X1,X1))),k2_enumset1(X1,X1,X1,X1)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_47]),c_0_65]),c_0_66]),c_0_25]),c_0_25]),c_0_67]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49])).

fof(c_0_75,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | X4 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_76,negated_conjecture,
    ( k3_yellow_0(k2_yellow_1(k1_zfmisc_1(esk3_0))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_77,plain,
    ( k3_yellow_0(k2_yellow_1(k1_zfmisc_1(X1))) = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])])).

cnf(c_0_78,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_79,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_81,plain,
    ( ~ r1_tarski(k1_zfmisc_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_71])).

cnf(c_0_82,negated_conjecture,
    ( k1_zfmisc_1(esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_72])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:32:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 10.32/10.49  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 10.32/10.49  # and selection function PSelectComplexExceptUniqMaxHorn.
% 10.32/10.49  #
% 10.32/10.49  # Preprocessing time       : 0.029 s
% 10.32/10.49  
% 10.32/10.49  # Failure: Out of unprocessed clauses!
% 10.32/10.49  # Parsed axioms                        : 27
% 10.32/10.49  # Removed by relevancy pruning/SinE    : 0
% 10.32/10.49  # Initial clauses                      : 44
% 10.32/10.49  # Removed in clause preprocessing      : 10
% 10.32/10.49  # Initial clauses in saturation        : 34
% 10.32/10.49  # Processed clauses                    : 123
% 10.32/10.49  # ...of these trivial                  : 6
% 10.32/10.49  # ...subsumed                          : 30
% 10.32/10.49  # ...remaining for further processing  : 87
% 10.32/10.49  # Other redundant clauses eliminated   : 4
% 10.32/10.49  # Clauses deleted for lack of memory   : 26
% 10.32/10.49  # Backward-subsumed                    : 8
% 10.32/10.49  # Backward-rewritten                   : 1
% 10.32/10.49  # Generated clauses                    : 250
% 10.32/10.49  # ...of the previous two non-trivial   : 225
% 10.32/10.49  # Contextual simplify-reflections      : 3
% 10.32/10.49  # Paramodulations                      : 234
% 10.32/10.49  # Factorizations                       : 4
% 10.32/10.49  # Equation resolutions                 : 12
% 10.32/10.49  # Propositional unsat checks           : 0
% 10.32/10.49  #    Propositional check models        : 0
% 10.32/10.49  #    Propositional check unsatisfiable : 0
% 10.32/10.49  #    Propositional clauses             : 0
% 10.32/10.49  #    Propositional clauses after purity: 0
% 10.32/10.49  #    Propositional unsat core size     : 0
% 10.32/10.49  #    Propositional preprocessing time  : 0.000
% 10.32/10.49  #    Propositional encoding time       : 0.000
% 10.32/10.49  #    Propositional solver time         : 0.000
% 10.32/10.49  #    Success case prop preproc time    : 0.000
% 10.32/10.49  #    Success case prop encoding time   : 0.000
% 10.32/10.49  #    Success case prop solver time     : 0.000
% 10.32/10.49  # Current number of processed clauses  : 75
% 10.32/10.49  #    Positive orientable unit clauses  : 14
% 10.32/10.49  #    Positive unorientable unit clauses: 1
% 10.32/10.49  #    Negative unit clauses             : 13
% 10.32/10.49  #    Non-unit-clauses                  : 47
% 10.32/10.49  # Current number of unprocessed clauses: 0
% 10.32/10.49  # ...number of literals in the above   : 0
% 10.32/10.49  # Current number of archived formulas  : 0
% 10.32/10.49  # Current number of archived clauses   : 19
% 10.32/10.49  # Clause-clause subsumption calls (NU) : 284
% 10.32/10.49  # Rec. Clause-clause subsumption calls : 252
% 10.32/10.49  # Non-unit clause-clause subsumptions  : 30
% 10.32/10.49  # Unit Clause-clause subsumption calls : 52
% 10.32/10.49  # Rewrite failures with RHS unbound    : 0
% 10.32/10.49  # BW rewrite match attempts            : 10
% 10.32/10.49  # BW rewrite match successes           : 4
% 10.32/10.49  # Condensation attempts                : 0
% 10.32/10.49  # Condensation successes               : 0
% 10.32/10.49  # Termbank termtop insertions          : 30269374
% 10.45/10.63  # No success with AutoSched0
% 10.45/10.63  # Trying AutoSched1 for 131 seconds
% 10.45/10.64  # AutoSched1-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 10.45/10.64  # and selection function PSelectComplexExceptUniqMaxHorn.
% 10.45/10.64  #
% 10.45/10.64  # Preprocessing time       : 0.012 s
% 10.45/10.64  # Presaturation interreduction done
% 10.45/10.64  
% 10.45/10.64  # Proof found!
% 10.45/10.64  # SZS status Theorem
% 10.45/10.64  # SZS output start CNFRefutation
% 10.45/10.64  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 10.45/10.64  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 10.45/10.64  fof(t18_funct_1, axiom, ![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 10.45/10.64  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.45/10.64  fof(t18_yellow_1, conjecture, ![X1]:k3_yellow_0(k3_yellow_1(X1))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_yellow_1)).
% 10.45/10.64  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 10.45/10.64  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 10.45/10.64  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 10.45/10.64  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 10.45/10.64  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 10.45/10.64  fof(t93_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_zfmisc_1)).
% 10.45/10.64  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_yellow_1)).
% 10.45/10.64  fof(t4_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 10.45/10.64  fof(redefinition_k9_setfam_1, axiom, ![X1]:k9_setfam_1(X1)=k1_zfmisc_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 10.45/10.64  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 10.45/10.64  fof(t52_ordinal1, axiom, ![X1]:k6_subset_1(k1_ordinal1(X1),k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_ordinal1)).
% 10.45/10.64  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 10.45/10.64  fof(t13_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k1_xboole_0,X1)=>k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_1)).
% 10.45/10.64  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 10.45/10.64  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 10.45/10.64  fof(c_0_20, plain, ![X32, X33]:k1_setfam_1(k2_tarski(X32,X33))=k3_xboole_0(X32,X33), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 10.45/10.64  fof(c_0_21, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 10.45/10.64  fof(c_0_22, plain, ![X35, X36]:((((v1_relat_1(esk2_2(X35,X36))|X35=k1_xboole_0)&(v1_funct_1(esk2_2(X35,X36))|X35=k1_xboole_0))&((X36=k1_relat_1(esk2_2(X35,X36))|X35=k1_xboole_0)&(r1_tarski(k2_relat_1(esk2_2(X35,X36)),X35)|X35=k1_xboole_0)))&(((v1_relat_1(esk2_2(X35,X36))|X36!=k1_xboole_0)&(v1_funct_1(esk2_2(X35,X36))|X36!=k1_xboole_0))&((X36=k1_relat_1(esk2_2(X35,X36))|X36!=k1_xboole_0)&(r1_tarski(k2_relat_1(esk2_2(X35,X36)),X35)|X36!=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_funct_1])])])])).
% 10.45/10.64  fof(c_0_23, plain, ![X7, X8]:k4_xboole_0(X7,X8)=k5_xboole_0(X7,k3_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 10.45/10.64  cnf(c_0_24, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 10.45/10.64  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 10.45/10.64  fof(c_0_26, negated_conjecture, ~(![X1]:k3_yellow_0(k3_yellow_1(X1))=k1_xboole_0), inference(assume_negation,[status(cth)],[t18_yellow_1])).
% 10.45/10.64  fof(c_0_27, plain, ![X34]:((k1_relat_1(X34)!=k1_xboole_0|X34=k1_xboole_0|~v1_relat_1(X34))&(k2_relat_1(X34)!=k1_xboole_0|X34=k1_xboole_0|~v1_relat_1(X34))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 10.45/10.64  cnf(c_0_28, plain, (v1_relat_1(esk2_2(X1,X2))|X2!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 10.45/10.64  cnf(c_0_29, plain, (X1=k1_relat_1(esk2_2(X2,X1))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 10.45/10.64  fof(c_0_30, plain, ![X24, X25, X26]:(((r2_hidden(X24,X25)|~r2_hidden(X24,k4_xboole_0(X25,k1_tarski(X26))))&(X24!=X26|~r2_hidden(X24,k4_xboole_0(X25,k1_tarski(X26)))))&(~r2_hidden(X24,X25)|X24=X26|r2_hidden(X24,k4_xboole_0(X25,k1_tarski(X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 10.45/10.64  fof(c_0_31, plain, ![X11]:k2_tarski(X11,X11)=k1_tarski(X11), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 10.45/10.64  cnf(c_0_32, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 10.45/10.64  cnf(c_0_33, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 10.45/10.64  fof(c_0_34, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 10.45/10.64  fof(c_0_35, plain, ![X38]:k1_ordinal1(X38)=k2_xboole_0(X38,k1_tarski(X38)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 10.45/10.64  fof(c_0_36, plain, ![X27, X28]:k3_tarski(k2_tarski(X27,X28))=k2_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t93_zfmisc_1])).
% 10.45/10.64  fof(c_0_37, negated_conjecture, k3_yellow_0(k3_yellow_1(esk3_0))!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 10.45/10.64  fof(c_0_38, plain, ![X42]:k3_yellow_1(X42)=k3_lattice3(k1_lattice3(X42)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 10.45/10.64  fof(c_0_39, plain, ![X44]:k3_yellow_1(X44)=k2_yellow_1(k9_setfam_1(X44)), inference(variable_rename,[status(thm)],[t4_yellow_1])).
% 10.45/10.64  fof(c_0_40, plain, ![X41]:k9_setfam_1(X41)=k1_zfmisc_1(X41), inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).
% 10.45/10.64  fof(c_0_41, plain, ![X17, X18, X19, X20, X21, X22]:(((~r2_hidden(X19,X18)|r1_tarski(X19,X17)|X18!=k1_zfmisc_1(X17))&(~r1_tarski(X20,X17)|r2_hidden(X20,X18)|X18!=k1_zfmisc_1(X17)))&((~r2_hidden(esk1_2(X21,X22),X22)|~r1_tarski(esk1_2(X21,X22),X21)|X22=k1_zfmisc_1(X21))&(r2_hidden(esk1_2(X21,X22),X22)|r1_tarski(esk1_2(X21,X22),X21)|X22=k1_zfmisc_1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 10.45/10.64  cnf(c_0_42, plain, (r1_tarski(k2_relat_1(esk2_2(X1,X2)),X1)|X2!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 10.45/10.64  cnf(c_0_43, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 10.45/10.64  cnf(c_0_44, plain, (v1_relat_1(esk2_2(X1,k1_xboole_0))), inference(er,[status(thm)],[c_0_28])).
% 10.45/10.64  cnf(c_0_45, plain, (k1_relat_1(esk2_2(X1,k1_xboole_0))=k1_xboole_0), inference(er,[status(thm)],[c_0_29])).
% 10.45/10.64  cnf(c_0_46, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 10.45/10.64  cnf(c_0_47, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 10.45/10.64  cnf(c_0_48, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 10.45/10.64  cnf(c_0_49, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 10.45/10.64  fof(c_0_50, plain, ![X40]:k6_subset_1(k1_ordinal1(X40),k1_tarski(X40))=X40, inference(variable_rename,[status(thm)],[t52_ordinal1])).
% 10.45/10.64  fof(c_0_51, plain, ![X30, X31]:k6_subset_1(X30,X31)=k4_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 10.45/10.64  cnf(c_0_52, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 10.45/10.64  cnf(c_0_53, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 10.45/10.64  cnf(c_0_54, negated_conjecture, (k3_yellow_0(k3_yellow_1(esk3_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 10.45/10.64  cnf(c_0_55, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 10.45/10.64  cnf(c_0_56, plain, (k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 10.45/10.64  cnf(c_0_57, plain, (k9_setfam_1(X1)=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 10.45/10.64  fof(c_0_58, plain, ![X43]:(v1_xboole_0(X43)|(~r2_hidden(k1_xboole_0,X43)|k3_yellow_0(k2_yellow_1(X43))=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t13_yellow_1])])])).
% 10.45/10.64  cnf(c_0_59, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 10.45/10.64  cnf(c_0_60, plain, (r1_tarski(k2_relat_1(esk2_2(X1,k1_xboole_0)),X1)), inference(er,[status(thm)],[c_0_42])).
% 10.45/10.64  cnf(c_0_61, plain, (esk2_2(X1,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 10.45/10.64  cnf(c_0_62, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 10.45/10.64  cnf(c_0_63, plain, (X1!=X2|~r2_hidden(X1,k5_xboole_0(X3,k1_setfam_1(k2_enumset1(X3,X3,X3,k2_enumset1(X2,X2,X2,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_25]), c_0_48]), c_0_49]), c_0_49])).
% 10.45/10.64  cnf(c_0_64, plain, (k6_subset_1(k1_ordinal1(X1),k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 10.45/10.64  cnf(c_0_65, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 10.45/10.64  cnf(c_0_66, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_52, c_0_47])).
% 10.45/10.64  cnf(c_0_67, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_53, c_0_25])).
% 10.45/10.64  cnf(c_0_68, negated_conjecture, (k3_yellow_0(k3_lattice3(k1_lattice3(esk3_0)))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 10.45/10.64  cnf(c_0_69, plain, (k2_yellow_1(k1_zfmisc_1(X1))=k3_lattice3(k1_lattice3(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57]), c_0_55])).
% 10.45/10.64  cnf(c_0_70, plain, (v1_xboole_0(X1)|k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0|~r2_hidden(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 10.45/10.64  cnf(c_0_71, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_59])).
% 10.45/10.64  cnf(c_0_72, plain, (r1_tarski(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 10.45/10.64  cnf(c_0_73, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_enumset1(X2,X2,X2,k2_enumset1(X1,X1,X1,X1)))))), inference(er,[status(thm)],[c_0_63])).
% 10.45/10.64  cnf(c_0_74, plain, (k5_xboole_0(k3_tarski(k2_enumset1(X1,X1,X1,k2_enumset1(X1,X1,X1,X1))),k1_setfam_1(k2_enumset1(k3_tarski(k2_enumset1(X1,X1,X1,k2_enumset1(X1,X1,X1,X1))),k3_tarski(k2_enumset1(X1,X1,X1,k2_enumset1(X1,X1,X1,X1))),k3_tarski(k2_enumset1(X1,X1,X1,k2_enumset1(X1,X1,X1,X1))),k2_enumset1(X1,X1,X1,X1))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_47]), c_0_65]), c_0_66]), c_0_25]), c_0_25]), c_0_67]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49])).
% 10.45/10.64  fof(c_0_75, plain, ![X4]:(~v1_xboole_0(X4)|X4=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 10.45/10.64  cnf(c_0_76, negated_conjecture, (k3_yellow_0(k2_yellow_1(k1_zfmisc_1(esk3_0)))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 10.45/10.64  cnf(c_0_77, plain, (k3_yellow_0(k2_yellow_1(k1_zfmisc_1(X1)))=k1_xboole_0|v1_xboole_0(k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])])).
% 10.45/10.64  cnf(c_0_78, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 10.45/10.64  cnf(c_0_79, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 10.45/10.64  cnf(c_0_80, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 10.45/10.64  cnf(c_0_81, plain, (~r1_tarski(k1_zfmisc_1(X1),X1)), inference(spm,[status(thm)],[c_0_78, c_0_71])).
% 10.45/10.64  cnf(c_0_82, negated_conjecture, (k1_zfmisc_1(esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 10.45/10.64  cnf(c_0_83, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_72])]), ['proof']).
% 10.45/10.64  # SZS output end CNFRefutation
% 10.45/10.64  # Proof object total steps             : 84
% 10.45/10.64  # Proof object clause steps            : 44
% 10.45/10.64  # Proof object formula steps           : 40
% 10.45/10.64  # Proof object conjectures             : 9
% 10.45/10.64  # Proof object clause conjectures      : 6
% 10.45/10.64  # Proof object formula conjectures     : 3
% 10.45/10.64  # Proof object initial clauses used    : 22
% 10.45/10.64  # Proof object initial formulas used   : 20
% 10.45/10.64  # Proof object generating inferences   : 7
% 10.45/10.64  # Proof object simplifying inferences  : 41
% 10.45/10.64  # Training examples: 0 positive, 0 negative
% 10.45/10.64  # Parsed axioms                        : 27
% 10.45/10.64  # Removed by relevancy pruning/SinE    : 0
% 10.45/10.64  # Initial clauses                      : 44
% 10.45/10.64  # Removed in clause preprocessing      : 10
% 10.45/10.64  # Initial clauses in saturation        : 34
% 10.45/10.64  # Processed clauses                    : 84
% 10.45/10.64  # ...of these trivial                  : 0
% 10.45/10.64  # ...subsumed                          : 0
% 10.45/10.64  # ...remaining for further processing  : 84
% 10.45/10.64  # Other redundant clauses eliminated   : 10
% 10.45/10.64  # Clauses deleted for lack of memory   : 0
% 10.45/10.64  # Backward-subsumed                    : 0
% 10.45/10.64  # Backward-rewritten                   : 5
% 10.45/10.64  # Generated clauses                    : 39
% 10.45/10.64  # ...of the previous two non-trivial   : 29
% 10.45/10.64  # Contextual simplify-reflections      : 0
% 10.45/10.64  # Paramodulations                      : 29
% 10.45/10.64  # Factorizations                       : 0
% 10.45/10.64  # Equation resolutions                 : 10
% 10.45/10.64  # Propositional unsat checks           : 0
% 10.45/10.64  #    Propositional check models        : 0
% 10.45/10.64  #    Propositional check unsatisfiable : 0
% 10.45/10.64  #    Propositional clauses             : 0
% 10.45/10.64  #    Propositional clauses after purity: 0
% 10.45/10.64  #    Propositional unsat core size     : 0
% 10.45/10.64  #    Propositional preprocessing time  : 0.000
% 10.45/10.64  #    Propositional encoding time       : 0.000
% 10.45/10.64  #    Propositional solver time         : 0.000
% 10.45/10.64  #    Success case prop preproc time    : 0.000
% 10.45/10.64  #    Success case prop encoding time   : 0.000
% 10.45/10.64  #    Success case prop solver time     : 0.000
% 10.45/10.64  # Current number of processed clauses  : 37
% 10.45/10.64  #    Positive orientable unit clauses  : 14
% 10.45/10.64  #    Positive unorientable unit clauses: 1
% 10.45/10.64  #    Negative unit clauses             : 3
% 10.45/10.64  #    Non-unit-clauses                  : 19
% 10.45/10.64  # Current number of unprocessed clauses: 7
% 10.45/10.64  # ...number of literals in the above   : 19
% 10.45/10.64  # Current number of archived formulas  : 0
% 10.45/10.64  # Current number of archived clauses   : 48
% 10.45/10.64  # Clause-clause subsumption calls (NU) : 98
% 10.45/10.64  # Rec. Clause-clause subsumption calls : 94
% 10.45/10.64  # Non-unit clause-clause subsumptions  : 0
% 10.45/10.64  # Unit Clause-clause subsumption calls : 13
% 10.45/10.64  # Rewrite failures with RHS unbound    : 0
% 10.45/10.64  # BW rewrite match attempts            : 5
% 10.45/10.64  # BW rewrite match successes           : 4
% 10.45/10.64  # Condensation attempts                : 0
% 10.45/10.64  # Condensation successes               : 0
% 10.45/10.64  # Termbank termtop insertions          : 2465
% 10.45/10.64  
% 10.45/10.64  # -------------------------------------------------
% 10.45/10.64  # User time                : 9.021 s
% 10.45/10.64  # System time              : 1.282 s
% 10.45/10.64  # Total time               : 10.304 s
% 10.45/10.64  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
