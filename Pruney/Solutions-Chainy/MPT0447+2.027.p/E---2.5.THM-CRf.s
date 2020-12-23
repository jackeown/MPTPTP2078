%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:25 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 735 expanded)
%              Number of clauses        :   97 ( 356 expanded)
%              Number of leaves         :   23 ( 184 expanded)
%              Depth                    :   15
%              Number of atoms          :  304 (1526 expanded)
%              Number of equality atoms :   60 ( 441 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t31_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(t26_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

fof(t15_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(c_0_23,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r1_xboole_0(X7,X8)
        | r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)) )
      & ( ~ r2_hidden(X12,k3_xboole_0(X10,X11))
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_24,plain,(
    ! [X47,X48] : k1_setfam_1(k2_tarski(X47,X48)) = k3_xboole_0(X47,X48) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_25,plain,(
    ! [X26,X27] :
      ( ~ r1_tarski(X26,X27)
      | k3_xboole_0(X26,X27) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_26,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(k2_xboole_0(X20,X21),X22)
      | r1_tarski(X20,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_27,plain,(
    ! [X43,X44] : k3_tarski(k2_tarski(X43,X44)) = k2_xboole_0(X43,X44) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_28,plain,(
    ! [X32,X33,X34] :
      ( ~ r1_tarski(k4_xboole_0(X32,X33),X34)
      | r1_tarski(X32,k2_xboole_0(X33,X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

fof(c_0_29,plain,(
    ! [X36,X37] : r1_tarski(X36,k2_xboole_0(X36,X37)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,plain,(
    ! [X5,X6] :
      ( ~ r1_xboole_0(X5,X6)
      | r1_xboole_0(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_34,plain,(
    ! [X35] : r1_xboole_0(X35,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_38,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_40,plain,(
    ! [X38,X39,X40] :
      ( ~ r1_tarski(X38,X39)
      | ~ r1_tarski(X40,X39)
      | r1_tarski(k2_xboole_0(X38,X40),X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_41,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_42,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_31])).

fof(c_0_43,plain,(
    ! [X28] : r1_tarski(k1_xboole_0,X28) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_44,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k3_tarski(k2_tarski(X1,X2)),X3) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_39,c_0_36])).

cnf(c_0_51,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_52,plain,(
    ! [X41,X42] : k2_tarski(X41,X42) = k2_tarski(X42,X41) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_53,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_relat_1])).

fof(c_0_54,plain,(
    ! [X29,X30,X31] :
      ( ~ r1_tarski(X29,k2_xboole_0(X30,X31))
      | r1_tarski(k4_xboole_0(X29,X30),X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_55,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_58,plain,(
    ! [X49,X50,X51,X53,X54,X55,X56,X58] :
      ( ( ~ r2_hidden(X51,X50)
        | r2_hidden(k4_tarski(X51,esk3_3(X49,X50,X51)),X49)
        | X50 != k1_relat_1(X49) )
      & ( ~ r2_hidden(k4_tarski(X53,X54),X49)
        | r2_hidden(X53,X50)
        | X50 != k1_relat_1(X49) )
      & ( ~ r2_hidden(esk4_2(X55,X56),X56)
        | ~ r2_hidden(k4_tarski(esk4_2(X55,X56),X58),X55)
        | X56 = k1_relat_1(X55) )
      & ( r2_hidden(esk4_2(X55,X56),X56)
        | r2_hidden(k4_tarski(esk4_2(X55,X56),esk5_2(X55,X56)),X55)
        | X56 = k1_relat_1(X55) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_59,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,X18)
      | r1_tarski(X17,k2_xboole_0(X19,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X1,X4)),X2),X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_62,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(k3_tarski(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_63,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_51,c_0_36])).

cnf(c_0_64,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_65,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,X24)
      | ~ r1_tarski(X24,X25)
      | r1_tarski(X23,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_66,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_relat_1(esk7_0)
    & r1_tarski(esk6_0,esk7_0)
    & ~ r1_tarski(k3_relat_1(esk6_0),k3_relat_1(esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_53])])])).

cnf(c_0_67,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_69,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,k4_xboole_0(k3_tarski(k2_tarski(X1,X3)),X2)))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_72,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_61])])).

cnf(c_0_73,plain,
    ( X1 = k3_tarski(k2_tarski(X2,X3))
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X3,X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_63])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_64])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_77,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_67,c_0_36])).

cnf(c_0_78,plain,
    ( X1 != k1_relat_1(k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

fof(c_0_79,plain,(
    ! [X13] :
      ( X13 = k1_xboole_0
      | r2_hidden(esk2_1(X13),X13) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_70,c_0_36])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X1,X3)),X2),X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_82,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_61])])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(X1,esk7_0)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_84,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1),X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_61])).

cnf(c_0_85,plain,
    ( ~ r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_86,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_75,c_0_80])).

cnf(c_0_88,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k4_xboole_0(X3,X2),X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X1,esk6_0)),X1),esk7_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

fof(c_0_90,plain,(
    ! [X60] :
      ( ~ v1_relat_1(X60)
      | k3_relat_1(X60) = k2_xboole_0(k1_relat_1(X60),k2_relat_1(X60)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_91,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_92,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_93,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_87,c_0_72])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(X1,esk7_0)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(esk7_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_95,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_56])).

cnf(c_0_96,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

fof(c_0_97,plain,(
    ! [X63,X64] :
      ( ~ v1_relat_1(X63)
      | ~ v1_relat_1(X64)
      | k2_relat_1(k2_xboole_0(X63,X64)) = k2_xboole_0(k2_relat_1(X63),k2_relat_1(X64)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_relat_1])])])).

cnf(c_0_98,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_84])).

cnf(c_0_99,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_78,c_0_91])).

cnf(c_0_100,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_92,c_0_31])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | ~ r1_tarski(esk7_0,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_76])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(X1,esk7_0)
    | ~ r1_tarski(k4_xboole_0(X1,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_47])).

cnf(c_0_103,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_95,c_0_84])).

cnf(c_0_104,plain,
    ( k3_relat_1(X1) = k3_tarski(k2_tarski(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_96,c_0_36])).

cnf(c_0_105,plain,
    ( k2_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_106,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k4_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_98,c_0_47])).

fof(c_0_107,plain,(
    ! [X61,X62] :
      ( ~ v1_relat_1(X61)
      | ~ v1_relat_1(X62)
      | r1_tarski(k6_subset_1(k1_relat_1(X61),k1_relat_1(X62)),k1_relat_1(k6_subset_1(X61,X62))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_relat_1])])])).

fof(c_0_108,plain,(
    ! [X45,X46] : k6_subset_1(X45,X46) = k4_xboole_0(X45,X46) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_109,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_86])).

cnf(c_0_110,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_64])).

cnf(c_0_111,plain,
    ( r1_xboole_0(X1,X2)
    | k1_setfam_1(k2_tarski(X1,X2)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_112,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_64])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | ~ r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_101,c_0_61])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(k1_xboole_0,esk7_0)),esk7_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_56])]),c_0_64])).

cnf(c_0_115,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk6_0),k3_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_116,plain,
    ( r1_tarski(k3_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_104])).

cnf(c_0_117,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_118,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(X1,X2))) = k3_tarski(k2_tarski(k2_relat_1(X1),k2_relat_1(X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_36]),c_0_36])).

cnf(c_0_119,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk7_0,esk6_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_89])).

cnf(c_0_120,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_121,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_122,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_123,plain,
    ( r1_xboole_0(X1,X2)
    | X1 != k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_111,c_0_42])).

cnf(c_0_124,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk6_0,X1),X2)
    | ~ r1_tarski(esk7_0,k3_tarski(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_125,negated_conjecture,
    ( k3_tarski(k2_tarski(k1_xboole_0,esk7_0)) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_114]),c_0_74])])).

cnf(c_0_126,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk6_0),k3_relat_1(esk7_0))
    | ~ r1_tarski(k1_relat_1(esk6_0),k3_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117])])).

cnf(c_0_127,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_104])).

cnf(c_0_128,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_129,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(k3_tarski(k2_tarski(X2,X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_118])).

cnf(c_0_130,negated_conjecture,
    ( k3_tarski(k2_tarski(esk7_0,esk6_0)) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_119]),c_0_50])])).

cnf(c_0_131,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_121]),c_0_121])).

cnf(c_0_132,plain,
    ( X1 = k1_xboole_0
    | X2 != k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_133,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk6_0,esk7_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_61])])).

cnf(c_0_134,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk6_0),k3_relat_1(esk7_0))
    | ~ r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_128])])).

cnf(c_0_135,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_117]),c_0_128])])).

cnf(c_0_136,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_50])).

cnf(c_0_137,plain,
    ( k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) = k1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_131])).

cnf(c_0_138,negated_conjecture,
    ( k4_xboole_0(esk6_0,esk7_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_56])])).

cnf(c_0_139,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk6_0),k3_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_134,c_0_135])])).

cnf(c_0_140,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_136,c_0_104])).

cnf(c_0_141,negated_conjecture,
    ( k4_xboole_0(k1_relat_1(esk6_0),k1_relat_1(esk7_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_91]),c_0_128]),c_0_117]),c_0_91]),c_0_56])])).

cnf(c_0_142,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_128])])).

cnf(c_0_143,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_141]),c_0_56])]),c_0_142]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:38:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 3.58/3.79  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 3.58/3.79  # and selection function PSelectComplexExceptUniqMaxHorn.
% 3.58/3.79  #
% 3.58/3.79  # Preprocessing time       : 0.028 s
% 3.58/3.79  
% 3.58/3.79  # Proof found!
% 3.58/3.79  # SZS status Theorem
% 3.58/3.79  # SZS output start CNFRefutation
% 3.58/3.79  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.58/3.79  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.58/3.79  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.58/3.79  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.58/3.79  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.58/3.79  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 3.58/3.79  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.58/3.79  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.58/3.79  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.58/3.79  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.58/3.79  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.58/3.79  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.58/3.79  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.58/3.79  fof(t31_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 3.58/3.79  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 3.58/3.79  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.58/3.79  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.58/3.79  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.58/3.79  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.58/3.79  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 3.58/3.79  fof(t26_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_relat_1)).
% 3.58/3.79  fof(t15_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_relat_1)).
% 3.58/3.79  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.58/3.79  fof(c_0_23, plain, ![X7, X8, X10, X11, X12]:((r1_xboole_0(X7,X8)|r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)))&(~r2_hidden(X12,k3_xboole_0(X10,X11))|~r1_xboole_0(X10,X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 3.58/3.79  fof(c_0_24, plain, ![X47, X48]:k1_setfam_1(k2_tarski(X47,X48))=k3_xboole_0(X47,X48), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 3.58/3.79  fof(c_0_25, plain, ![X26, X27]:(~r1_tarski(X26,X27)|k3_xboole_0(X26,X27)=X26), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 3.58/3.79  fof(c_0_26, plain, ![X20, X21, X22]:(~r1_tarski(k2_xboole_0(X20,X21),X22)|r1_tarski(X20,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 3.58/3.79  fof(c_0_27, plain, ![X43, X44]:k3_tarski(k2_tarski(X43,X44))=k2_xboole_0(X43,X44), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 3.58/3.79  fof(c_0_28, plain, ![X32, X33, X34]:(~r1_tarski(k4_xboole_0(X32,X33),X34)|r1_tarski(X32,k2_xboole_0(X33,X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 3.58/3.79  fof(c_0_29, plain, ![X36, X37]:r1_tarski(X36,k2_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 3.58/3.79  cnf(c_0_30, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.58/3.79  cnf(c_0_31, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 3.58/3.79  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.58/3.79  fof(c_0_33, plain, ![X5, X6]:(~r1_xboole_0(X5,X6)|r1_xboole_0(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 3.58/3.79  fof(c_0_34, plain, ![X35]:r1_xboole_0(X35,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 3.58/3.79  cnf(c_0_35, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 3.58/3.79  cnf(c_0_36, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 3.58/3.79  cnf(c_0_37, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.58/3.79  fof(c_0_38, plain, ![X15, X16]:(((r1_tarski(X15,X16)|X15!=X16)&(r1_tarski(X16,X15)|X15!=X16))&(~r1_tarski(X15,X16)|~r1_tarski(X16,X15)|X15=X16)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 3.58/3.79  cnf(c_0_39, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 3.58/3.79  fof(c_0_40, plain, ![X38, X39, X40]:(~r1_tarski(X38,X39)|~r1_tarski(X40,X39)|r1_tarski(k2_xboole_0(X38,X40),X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 3.58/3.79  cnf(c_0_41, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 3.58/3.79  cnf(c_0_42, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_31])).
% 3.58/3.79  fof(c_0_43, plain, ![X28]:r1_tarski(k1_xboole_0,X28), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 3.58/3.79  cnf(c_0_44, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 3.58/3.79  cnf(c_0_45, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 3.58/3.79  cnf(c_0_46, plain, (r1_tarski(X1,X3)|~r1_tarski(k3_tarski(k2_tarski(X1,X2)),X3)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 3.58/3.79  cnf(c_0_47, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_37, c_0_36])).
% 3.58/3.79  cnf(c_0_48, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 3.58/3.79  cnf(c_0_49, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 3.58/3.79  cnf(c_0_50, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_39, c_0_36])).
% 3.58/3.79  cnf(c_0_51, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 3.58/3.79  fof(c_0_52, plain, ![X41, X42]:k2_tarski(X41,X42)=k2_tarski(X42,X41), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 3.58/3.79  fof(c_0_53, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t31_relat_1])).
% 3.58/3.79  fof(c_0_54, plain, ![X29, X30, X31]:(~r1_tarski(X29,k2_xboole_0(X30,X31))|r1_tarski(k4_xboole_0(X29,X30),X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 3.58/3.79  cnf(c_0_55, plain, (~r1_tarski(X1,X2)|~r2_hidden(X3,X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 3.58/3.79  cnf(c_0_56, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.58/3.79  cnf(c_0_57, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 3.58/3.79  fof(c_0_58, plain, ![X49, X50, X51, X53, X54, X55, X56, X58]:(((~r2_hidden(X51,X50)|r2_hidden(k4_tarski(X51,esk3_3(X49,X50,X51)),X49)|X50!=k1_relat_1(X49))&(~r2_hidden(k4_tarski(X53,X54),X49)|r2_hidden(X53,X50)|X50!=k1_relat_1(X49)))&((~r2_hidden(esk4_2(X55,X56),X56)|~r2_hidden(k4_tarski(esk4_2(X55,X56),X58),X55)|X56=k1_relat_1(X55))&(r2_hidden(esk4_2(X55,X56),X56)|r2_hidden(k4_tarski(esk4_2(X55,X56),esk5_2(X55,X56)),X55)|X56=k1_relat_1(X55)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 3.58/3.79  fof(c_0_59, plain, ![X17, X18, X19]:(~r1_tarski(X17,X18)|r1_tarski(X17,k2_xboole_0(X19,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 3.58/3.79  cnf(c_0_60, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X1,X4)),X2),X3)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 3.58/3.79  cnf(c_0_61, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_48])).
% 3.58/3.79  cnf(c_0_62, plain, (k3_tarski(k2_tarski(X1,X2))=X1|~r1_tarski(k3_tarski(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 3.58/3.79  cnf(c_0_63, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_51, c_0_36])).
% 3.58/3.79  cnf(c_0_64, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 3.58/3.79  fof(c_0_65, plain, ![X23, X24, X25]:(~r1_tarski(X23,X24)|~r1_tarski(X24,X25)|r1_tarski(X23,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 3.58/3.79  fof(c_0_66, negated_conjecture, (v1_relat_1(esk6_0)&(v1_relat_1(esk7_0)&(r1_tarski(esk6_0,esk7_0)&~r1_tarski(k3_relat_1(esk6_0),k3_relat_1(esk7_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_53])])])).
% 3.58/3.79  cnf(c_0_67, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 3.58/3.79  cnf(c_0_68, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 3.58/3.79  cnf(c_0_69, plain, (r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 3.58/3.79  cnf(c_0_70, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 3.58/3.79  cnf(c_0_71, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,k4_xboole_0(k3_tarski(k2_tarski(X1,X3)),X2))))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 3.58/3.79  cnf(c_0_72, plain, (k3_tarski(k2_tarski(X1,X2))=X1|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_61])])).
% 3.58/3.79  cnf(c_0_73, plain, (X1=k3_tarski(k2_tarski(X2,X3))|~r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X3,X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_49, c_0_63])).
% 3.58/3.79  cnf(c_0_74, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_50, c_0_64])).
% 3.58/3.79  cnf(c_0_75, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 3.58/3.79  cnf(c_0_76, negated_conjecture, (r1_tarski(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 3.58/3.79  cnf(c_0_77, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))), inference(rw,[status(thm)],[c_0_67, c_0_36])).
% 3.58/3.79  cnf(c_0_78, plain, (X1!=k1_relat_1(k1_xboole_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 3.58/3.79  fof(c_0_79, plain, ![X13]:(X13=k1_xboole_0|r2_hidden(esk2_1(X13),X13)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 3.58/3.79  cnf(c_0_80, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_70, c_0_36])).
% 3.58/3.79  cnf(c_0_81, plain, (r1_tarski(X1,X2)|~r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X1,X3)),X2),X2)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 3.58/3.79  cnf(c_0_82, plain, (k3_tarski(k2_tarski(X1,X2))=X2|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_61])])).
% 3.58/3.79  cnf(c_0_83, negated_conjecture, (r1_tarski(X1,esk7_0)|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 3.58/3.79  cnf(c_0_84, plain, (r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1),X2)), inference(spm,[status(thm)],[c_0_77, c_0_61])).
% 3.58/3.79  cnf(c_0_85, plain, (~r2_hidden(X1,k1_relat_1(k1_xboole_0))), inference(er,[status(thm)],[c_0_78])).
% 3.58/3.79  cnf(c_0_86, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 3.58/3.79  cnf(c_0_87, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X1,X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_75, c_0_80])).
% 3.58/3.79  cnf(c_0_88, plain, (r1_tarski(X1,X2)|~r1_tarski(k4_xboole_0(X3,X2),X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 3.58/3.79  cnf(c_0_89, negated_conjecture, (r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X1,esk6_0)),X1),esk7_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 3.58/3.79  fof(c_0_90, plain, ![X60]:(~v1_relat_1(X60)|k3_relat_1(X60)=k2_xboole_0(k1_relat_1(X60),k2_relat_1(X60))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 3.58/3.79  cnf(c_0_91, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 3.58/3.79  cnf(c_0_92, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.58/3.79  cnf(c_0_93, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_tarski(X3,X4)|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_87, c_0_72])).
% 3.58/3.79  cnf(c_0_94, negated_conjecture, (r1_tarski(X1,esk7_0)|~r1_tarski(X1,k3_tarski(k2_tarski(esk7_0,esk6_0)))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 3.58/3.79  cnf(c_0_95, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_56])).
% 3.58/3.79  cnf(c_0_96, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 3.58/3.79  fof(c_0_97, plain, ![X63, X64]:(~v1_relat_1(X63)|(~v1_relat_1(X64)|k2_relat_1(k2_xboole_0(X63,X64))=k2_xboole_0(k2_relat_1(X63),k2_relat_1(X64)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_relat_1])])])).
% 3.58/3.79  cnf(c_0_98, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_tarski(k2_tarski(X2,X2)))), inference(spm,[status(thm)],[c_0_88, c_0_84])).
% 3.58/3.79  cnf(c_0_99, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_78, c_0_91])).
% 3.58/3.79  cnf(c_0_100, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_92, c_0_31])).
% 3.58/3.79  cnf(c_0_101, negated_conjecture, (r1_tarski(esk6_0,X1)|~r1_tarski(esk7_0,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_93, c_0_76])).
% 3.58/3.79  cnf(c_0_102, negated_conjecture, (r1_tarski(X1,esk7_0)|~r1_tarski(k4_xboole_0(X1,esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_94, c_0_47])).
% 3.58/3.79  cnf(c_0_103, plain, (k4_xboole_0(k3_tarski(k2_tarski(X1,k1_xboole_0)),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_95, c_0_84])).
% 3.58/3.79  cnf(c_0_104, plain, (k3_relat_1(X1)=k3_tarski(k2_tarski(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_96, c_0_36])).
% 3.58/3.79  cnf(c_0_105, plain, (k2_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 3.58/3.79  cnf(c_0_106, plain, (r1_tarski(X1,X2)|~r1_tarski(k4_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_98, c_0_47])).
% 3.58/3.79  fof(c_0_107, plain, ![X61, X62]:(~v1_relat_1(X61)|(~v1_relat_1(X62)|r1_tarski(k6_subset_1(k1_relat_1(X61),k1_relat_1(X62)),k1_relat_1(k6_subset_1(X61,X62))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_relat_1])])])).
% 3.58/3.79  fof(c_0_108, plain, ![X45, X46]:k6_subset_1(X45,X46)=k4_xboole_0(X45,X46), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 3.58/3.79  cnf(c_0_109, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_86])).
% 3.58/3.79  cnf(c_0_110, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_42, c_0_64])).
% 3.58/3.79  cnf(c_0_111, plain, (r1_xboole_0(X1,X2)|k1_setfam_1(k2_tarski(X1,X2))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 3.58/3.79  cnf(c_0_112, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))), inference(spm,[status(thm)],[c_0_77, c_0_64])).
% 3.58/3.79  cnf(c_0_113, negated_conjecture, (r1_tarski(esk6_0,X1)|~r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_101, c_0_61])).
% 3.58/3.79  cnf(c_0_114, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(k1_xboole_0,esk7_0)),esk7_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_56])]), c_0_64])).
% 3.58/3.79  cnf(c_0_115, negated_conjecture, (~r1_tarski(k3_relat_1(esk6_0),k3_relat_1(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 3.58/3.79  cnf(c_0_116, plain, (r1_tarski(k3_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_63, c_0_104])).
% 3.58/3.79  cnf(c_0_117, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 3.58/3.79  cnf(c_0_118, plain, (k2_relat_1(k3_tarski(k2_tarski(X1,X2)))=k3_tarski(k2_tarski(k2_relat_1(X1),k2_relat_1(X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_36]), c_0_36])).
% 3.58/3.79  cnf(c_0_119, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk7_0,esk6_0)),esk7_0)), inference(spm,[status(thm)],[c_0_106, c_0_89])).
% 3.58/3.79  cnf(c_0_120, plain, (r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_107])).
% 3.58/3.79  cnf(c_0_121, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_108])).
% 3.58/3.79  cnf(c_0_122, plain, (X1=k1_xboole_0|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 3.58/3.79  cnf(c_0_123, plain, (r1_xboole_0(X1,X2)|X1!=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_111, c_0_42])).
% 3.58/3.79  cnf(c_0_124, negated_conjecture, (r1_tarski(k4_xboole_0(esk6_0,X1),X2)|~r1_tarski(esk7_0,k3_tarski(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 3.58/3.79  cnf(c_0_125, negated_conjecture, (k3_tarski(k2_tarski(k1_xboole_0,esk7_0))=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_114]), c_0_74])])).
% 3.58/3.79  cnf(c_0_126, negated_conjecture, (~r1_tarski(k2_relat_1(esk6_0),k3_relat_1(esk7_0))|~r1_tarski(k1_relat_1(esk6_0),k3_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_117])])).
% 3.58/3.79  cnf(c_0_127, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_80, c_0_104])).
% 3.58/3.79  cnf(c_0_128, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 3.58/3.79  cnf(c_0_129, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(k3_tarski(k2_tarski(X2,X1))))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_74, c_0_118])).
% 3.58/3.79  cnf(c_0_130, negated_conjecture, (k3_tarski(k2_tarski(esk7_0,esk6_0))=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_119]), c_0_50])])).
% 3.58/3.79  cnf(c_0_131, plain, (r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k4_xboole_0(X1,X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_121]), c_0_121])).
% 3.58/3.79  cnf(c_0_132, plain, (X1=k1_xboole_0|X2!=k1_xboole_0|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_122, c_0_123])).
% 3.58/3.79  cnf(c_0_133, negated_conjecture, (r1_tarski(k4_xboole_0(esk6_0,esk7_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_61])])).
% 3.58/3.79  cnf(c_0_134, negated_conjecture, (~r1_tarski(k1_relat_1(esk6_0),k3_relat_1(esk7_0))|~r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_128])])).
% 3.58/3.79  cnf(c_0_135, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_117]), c_0_128])])).
% 3.58/3.79  cnf(c_0_136, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_75, c_0_50])).
% 3.58/3.79  cnf(c_0_137, plain, (k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=k1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))), inference(spm,[status(thm)],[c_0_49, c_0_131])).
% 3.58/3.79  cnf(c_0_138, negated_conjecture, (k4_xboole_0(esk6_0,esk7_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_133]), c_0_56])])).
% 3.58/3.79  cnf(c_0_139, negated_conjecture, (~r1_tarski(k1_relat_1(esk6_0),k3_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_134, c_0_135])])).
% 3.58/3.79  cnf(c_0_140, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_136, c_0_104])).
% 3.58/3.79  cnf(c_0_141, negated_conjecture, (k4_xboole_0(k1_relat_1(esk6_0),k1_relat_1(esk7_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_138]), c_0_91]), c_0_128]), c_0_117]), c_0_91]), c_0_56])])).
% 3.58/3.79  cnf(c_0_142, negated_conjecture, (~r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_140]), c_0_128])])).
% 3.58/3.79  cnf(c_0_143, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_141]), c_0_56])]), c_0_142]), ['proof']).
% 3.58/3.79  # SZS output end CNFRefutation
% 3.58/3.79  # Proof object total steps             : 144
% 3.58/3.79  # Proof object clause steps            : 97
% 3.58/3.79  # Proof object formula steps           : 47
% 3.58/3.79  # Proof object conjectures             : 27
% 3.58/3.79  # Proof object clause conjectures      : 24
% 3.58/3.79  # Proof object formula conjectures     : 3
% 3.58/3.79  # Proof object initial clauses used    : 28
% 3.58/3.79  # Proof object initial formulas used   : 23
% 3.58/3.79  # Proof object generating inferences   : 54
% 3.58/3.79  # Proof object simplifying inferences  : 53
% 3.58/3.79  # Training examples: 0 positive, 0 negative
% 3.58/3.79  # Parsed axioms                        : 23
% 3.58/3.79  # Removed by relevancy pruning/SinE    : 0
% 3.58/3.79  # Initial clauses                      : 32
% 3.58/3.79  # Removed in clause preprocessing      : 3
% 3.58/3.79  # Initial clauses in saturation        : 29
% 3.58/3.79  # Processed clauses                    : 12675
% 3.58/3.79  # ...of these trivial                  : 131
% 3.58/3.79  # ...subsumed                          : 9580
% 3.58/3.79  # ...remaining for further processing  : 2964
% 3.58/3.79  # Other redundant clauses eliminated   : 2
% 3.58/3.79  # Clauses deleted for lack of memory   : 0
% 3.58/3.79  # Backward-subsumed                    : 230
% 3.58/3.79  # Backward-rewritten                   : 61
% 3.58/3.79  # Generated clauses                    : 253386
% 3.58/3.79  # ...of the previous two non-trivial   : 235455
% 3.58/3.79  # Contextual simplify-reflections      : 38
% 3.58/3.79  # Paramodulations                      : 253349
% 3.58/3.79  # Factorizations                       : 4
% 3.58/3.79  # Equation resolutions                 : 31
% 3.58/3.79  # Propositional unsat checks           : 0
% 3.58/3.79  #    Propositional check models        : 0
% 3.58/3.79  #    Propositional check unsatisfiable : 0
% 3.58/3.79  #    Propositional clauses             : 0
% 3.58/3.79  #    Propositional clauses after purity: 0
% 3.58/3.79  #    Propositional unsat core size     : 0
% 3.58/3.79  #    Propositional preprocessing time  : 0.000
% 3.58/3.79  #    Propositional encoding time       : 0.000
% 3.58/3.79  #    Propositional solver time         : 0.000
% 3.58/3.79  #    Success case prop preproc time    : 0.000
% 3.58/3.79  #    Success case prop encoding time   : 0.000
% 3.58/3.79  #    Success case prop solver time     : 0.000
% 3.58/3.79  # Current number of processed clauses  : 2669
% 3.58/3.79  #    Positive orientable unit clauses  : 170
% 3.58/3.79  #    Positive unorientable unit clauses: 1
% 3.58/3.79  #    Negative unit clauses             : 24
% 3.58/3.79  #    Non-unit-clauses                  : 2474
% 3.58/3.79  # Current number of unprocessed clauses: 222170
% 3.58/3.79  # ...number of literals in the above   : 871673
% 3.58/3.79  # Current number of archived formulas  : 0
% 3.58/3.79  # Current number of archived clauses   : 296
% 3.58/3.79  # Clause-clause subsumption calls (NU) : 1220502
% 3.58/3.79  # Rec. Clause-clause subsumption calls : 385116
% 3.58/3.79  # Non-unit clause-clause subsumptions  : 6448
% 3.58/3.79  # Unit Clause-clause subsumption calls : 21992
% 3.58/3.79  # Rewrite failures with RHS unbound    : 0
% 3.58/3.79  # BW rewrite match attempts            : 20130
% 3.58/3.79  # BW rewrite match successes           : 29
% 3.58/3.79  # Condensation attempts                : 0
% 3.58/3.79  # Condensation successes               : 0
% 3.58/3.79  # Termbank termtop insertions          : 4746075
% 3.58/3.80  
% 3.58/3.80  # -------------------------------------------------
% 3.58/3.80  # User time                : 3.319 s
% 3.58/3.80  # System time              : 0.138 s
% 3.58/3.80  # Total time               : 3.457 s
% 3.58/3.80  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
