%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:25 EST 2020

% Result     : Theorem 13.27s
% Output     : CNFRefutation 13.27s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 444 expanded)
%              Number of clauses        :   84 ( 206 expanded)
%              Number of leaves         :   24 ( 114 expanded)
%              Depth                    :   18
%              Number of atoms          :  293 ( 795 expanded)
%              Number of equality atoms :   46 ( 273 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t31_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

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

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(t7_tarski,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ! [X4] :
                  ~ ( r2_hidden(X4,X2)
                    & r2_hidden(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t136_zfmisc_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( r2_hidden(X1,X2)
      & ! [X3,X4] :
          ( ( r2_hidden(X3,X2)
            & r1_tarski(X4,X3) )
         => r2_hidden(X4,X2) )
      & ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(k1_zfmisc_1(X3),X2) )
      & ! [X3] :
          ~ ( r1_tarski(X3,X2)
            & ~ r2_tarski(X3,X2)
            & ~ r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_zfmisc_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(t28_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_24,plain,(
    ! [X31,X32,X33] :
      ( ~ r1_tarski(X31,k2_xboole_0(X32,X33))
      | r1_tarski(k4_xboole_0(X31,X32),X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_25,plain,(
    ! [X45,X46] : k3_tarski(k2_tarski(X45,X46)) = k2_xboole_0(X45,X46) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_26,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_27,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_28,plain,(
    ! [X27,X28] : r1_tarski(k4_xboole_0(X27,X28),X27) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_29,plain,(
    ! [X22] : k2_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_30,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,X24)
      | ~ r1_tarski(X24,X25)
      | r1_tarski(X23,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_31,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_33,plain,(
    ! [X29,X30] : k2_xboole_0(X29,k4_xboole_0(X30,X29)) = k2_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_35,plain,(
    ! [X43,X44] : k2_tarski(X43,X44) = k2_tarski(X44,X43) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3),X1),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( k3_tarski(k2_tarski(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_40,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X3,X2)),X4),X3)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X1))) = k3_tarski(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_27]),c_0_27])).

cnf(c_0_43,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4),X3)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_40])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_43])).

fof(c_0_46,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_47,plain,(
    ! [X26] : r1_tarski(k1_xboole_0,X26) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(k3_tarski(k2_tarski(X2,X3)),k4_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_42])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_53,plain,(
    ! [X34,X35,X36] :
      ( ~ r1_tarski(k4_xboole_0(X34,X35),X36)
      | r1_tarski(X34,k2_xboole_0(X35,X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

fof(c_0_54,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_relat_1])).

fof(c_0_55,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_xboole_0(X11,X12) )
      & ( r2_hidden(esk2_2(X11,X12),X12)
        | r1_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_56,plain,(
    ! [X37] : r1_xboole_0(X37,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_57,plain,(
    ! [X70] :
      ( ~ v1_relat_1(X70)
      | k3_relat_1(X70) = k2_xboole_0(k1_relat_1(X70),k2_relat_1(X70)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(k3_tarski(k2_tarski(X2,X3)),k4_xboole_0(k4_xboole_0(X3,X2),X2))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_42])).

cnf(c_0_59,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_37]),c_0_39])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_61,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & v1_relat_1(esk9_0)
    & r1_tarski(esk8_0,esk9_0)
    & ~ r1_tarski(k3_relat_1(esk8_0),k3_relat_1(esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_54])])])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_64,plain,(
    ! [X53,X54,X56] :
      ( ( r2_hidden(esk4_2(X53,X54),X54)
        | ~ r2_hidden(X53,X54) )
      & ( ~ r2_hidden(X56,X54)
        | ~ r2_hidden(X56,esk4_2(X53,X54))
        | ~ r2_hidden(X53,X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).

fof(c_0_65,plain,(
    ! [X40,X41,X42] :
      ( ~ r1_tarski(X40,X41)
      | ~ r1_tarski(X42,X41)
      | r1_tarski(k2_xboole_0(X40,X42),X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_66,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_45])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_60,c_0_27])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_71,plain,(
    ! [X38,X39] : r1_tarski(X38,k2_xboole_0(X38,X39)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_73,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_74,plain,(
    ! [X47,X49,X50,X51,X52] :
      ( r2_hidden(X47,esk3_1(X47))
      & ( ~ r2_hidden(X49,esk3_1(X47))
        | ~ r1_tarski(X50,X49)
        | r2_hidden(X50,esk3_1(X47)) )
      & ( ~ r2_hidden(X51,esk3_1(X47))
        | r2_hidden(k1_zfmisc_1(X51),esk3_1(X47)) )
      & ( ~ r1_tarski(X52,esk3_1(X47))
        | r2_tarski(X52,esk3_1(X47))
        | r2_hidden(X52,esk3_1(X47)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t136_zfmisc_1])])])])])).

cnf(c_0_75,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_76,plain,
    ( k3_relat_1(X1) = k3_tarski(k2_tarski(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_66,c_0_27])).

fof(c_0_77,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,X20)
      | r1_tarski(X19,k2_xboole_0(X21,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_78,plain,(
    ! [X71,X72] :
      ( ~ v1_relat_1(X71)
      | ~ v1_relat_1(X72)
      | k1_relat_1(k2_xboole_0(X71,X72)) = k2_xboole_0(k1_relat_1(X71),k1_relat_1(X72)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relat_1])])])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k4_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(X1,esk9_0)
    | ~ r1_tarski(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_69])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_83,plain,
    ( ~ r2_hidden(esk4_2(X1,k1_xboole_0),X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,esk3_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

fof(c_0_85,plain,(
    ! [X59,X60,X61,X63,X64,X65,X66,X68] :
      ( ( ~ r2_hidden(X61,X60)
        | r2_hidden(k4_tarski(esk5_3(X59,X60,X61),X61),X59)
        | X60 != k2_relat_1(X59) )
      & ( ~ r2_hidden(k4_tarski(X64,X63),X59)
        | r2_hidden(X63,X60)
        | X60 != k2_relat_1(X59) )
      & ( ~ r2_hidden(esk6_2(X65,X66),X66)
        | ~ r2_hidden(k4_tarski(X68,esk6_2(X65,X66)),X65)
        | X66 = k2_relat_1(X65) )
      & ( r2_hidden(esk6_2(X65,X66),X66)
        | r2_hidden(k4_tarski(esk7_2(X65,X66),esk6_2(X65,X66)),X65)
        | X66 = k2_relat_1(X65) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_86,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_75,c_0_27])).

cnf(c_0_87,plain,
    ( k3_tarski(k2_tarski(k2_relat_1(X1),k1_relat_1(X1))) = k3_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_76,c_0_40])).

cnf(c_0_88,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_89,plain,
    ( k1_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(X1,esk9_0)
    | ~ r1_tarski(k4_xboole_0(X1,esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_91,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_81])).

cnf(c_0_92,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_82,c_0_27])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(X1,esk9_0)
    | ~ r1_tarski(X2,esk8_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_80])).

cnf(c_0_94,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_95,plain,
    ( r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_96,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk8_0),k3_relat_1(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_97,plain,
    ( r1_tarski(k3_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_98,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_99,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_88,c_0_27])).

cnf(c_0_100,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(X1,X2))) = k3_tarski(k2_tarski(k1_relat_1(X1),k1_relat_1(X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_27]),c_0_27])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk8_0,esk9_0)),esk9_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_40])).

cnf(c_0_102,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_40])).

fof(c_0_103,plain,(
    ! [X73,X74] :
      ( ~ v1_relat_1(X73)
      | ~ v1_relat_1(X74)
      | r1_tarski(k6_subset_1(k2_relat_1(X73),k2_relat_1(X74)),k2_relat_1(k6_subset_1(X73,X74))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_relat_1])])])).

fof(c_0_104,plain,(
    ! [X57,X58] : k6_subset_1(X57,X58) = k4_xboole_0(X57,X58) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_105,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_40])).

cnf(c_0_106,negated_conjecture,
    ( r1_tarski(X1,esk9_0)
    | ~ r1_tarski(X1,k4_xboole_0(esk8_0,X2)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_32])).

cnf(c_0_107,plain,
    ( X1 != k2_relat_1(k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

fof(c_0_108,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_109,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk8_0),k3_relat_1(esk9_0))
    | ~ r1_tarski(k2_relat_1(esk8_0),k3_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])])).

cnf(c_0_110,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_87])).

cnf(c_0_111,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_112,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(k3_tarski(k2_tarski(X1,X2))))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_100])).

cnf(c_0_113,negated_conjecture,
    ( k3_tarski(k2_tarski(esk8_0,esk9_0)) = esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_101]),c_0_102])])).

cnf(c_0_114,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_115,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_116,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(k4_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_105,c_0_68])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk8_0,X1),esk9_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_81])).

cnf(c_0_118,plain,
    ( ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_107])).

cnf(c_0_119,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_120,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk8_0),k3_relat_1(esk9_0))
    | ~ r1_tarski(k1_relat_1(esk8_0),k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_111])])).

cnf(c_0_121,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk8_0),k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_111]),c_0_98])])).

cnf(c_0_122,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_92])).

cnf(c_0_123,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_115]),c_0_115])).

cnf(c_0_124,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk8_0,esk9_0),X1) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_125,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_126,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk8_0),k3_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_121])])).

cnf(c_0_127,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_122,c_0_87])).

cnf(c_0_128,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1(X1),k2_relat_1(k4_xboole_0(X1,X2))),k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_116,c_0_123])).

cnf(c_0_129,negated_conjecture,
    ( k4_xboole_0(esk8_0,esk9_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_124])).

cnf(c_0_130,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_125])).

cnf(c_0_131,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk8_0),k2_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_111])])).

cnf(c_0_132,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_130]),c_0_45]),c_0_111]),c_0_98])]),c_0_131]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:42:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 13.27/13.47  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 13.27/13.47  # and selection function PSelectComplexExceptUniqMaxHorn.
% 13.27/13.47  #
% 13.27/13.47  # Preprocessing time       : 0.030 s
% 13.27/13.47  
% 13.27/13.47  # Proof found!
% 13.27/13.47  # SZS status Theorem
% 13.27/13.47  # SZS output start CNFRefutation
% 13.27/13.47  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 13.27/13.47  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 13.27/13.47  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 13.27/13.47  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 13.27/13.47  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 13.27/13.47  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 13.27/13.47  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 13.27/13.47  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.27/13.47  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.27/13.47  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 13.27/13.47  fof(t31_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 13.27/13.47  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 13.27/13.47  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 13.27/13.47  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 13.27/13.47  fof(t7_tarski, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X2)&r2_hidden(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 13.27/13.47  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 13.27/13.47  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 13.27/13.47  fof(t136_zfmisc_1, axiom, ![X1]:?[X2]:(((r2_hidden(X1,X2)&![X3, X4]:((r2_hidden(X3,X2)&r1_tarski(X4,X3))=>r2_hidden(X4,X2)))&![X3]:(r2_hidden(X3,X2)=>r2_hidden(k1_zfmisc_1(X3),X2)))&![X3]:~(((r1_tarski(X3,X2)&~(r2_tarski(X3,X2)))&~(r2_hidden(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t136_zfmisc_1)).
% 13.27/13.47  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 13.27/13.47  fof(t13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relat_1)).
% 13.27/13.47  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 13.27/13.47  fof(t28_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_relat_1)).
% 13.27/13.47  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 13.27/13.47  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 13.27/13.47  fof(c_0_24, plain, ![X31, X32, X33]:(~r1_tarski(X31,k2_xboole_0(X32,X33))|r1_tarski(k4_xboole_0(X31,X32),X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 13.27/13.47  fof(c_0_25, plain, ![X45, X46]:k3_tarski(k2_tarski(X45,X46))=k2_xboole_0(X45,X46), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 13.27/13.47  cnf(c_0_26, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 13.27/13.47  cnf(c_0_27, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 13.27/13.47  fof(c_0_28, plain, ![X27, X28]:r1_tarski(k4_xboole_0(X27,X28),X27), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 13.27/13.47  fof(c_0_29, plain, ![X22]:k2_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t1_boole])).
% 13.27/13.47  fof(c_0_30, plain, ![X23, X24, X25]:(~r1_tarski(X23,X24)|~r1_tarski(X24,X25)|r1_tarski(X23,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 13.27/13.47  cnf(c_0_31, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 13.27/13.47  cnf(c_0_32, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 13.27/13.47  fof(c_0_33, plain, ![X29, X30]:k2_xboole_0(X29,k4_xboole_0(X30,X29))=k2_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 13.27/13.47  cnf(c_0_34, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 13.27/13.47  fof(c_0_35, plain, ![X43, X44]:k2_tarski(X43,X44)=k2_tarski(X44,X43), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 13.27/13.47  cnf(c_0_36, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 13.27/13.47  cnf(c_0_37, plain, (r1_tarski(k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3),X1),X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 13.27/13.47  cnf(c_0_38, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 13.27/13.47  cnf(c_0_39, plain, (k3_tarski(k2_tarski(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_34, c_0_27])).
% 13.27/13.47  cnf(c_0_40, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 13.27/13.47  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X3,X2)),X4),X3))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 13.27/13.47  cnf(c_0_42, plain, (k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X1)))=k3_tarski(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_27]), c_0_27])).
% 13.27/13.47  cnf(c_0_43, plain, (k3_tarski(k2_tarski(k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 13.27/13.47  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X2,X3)),X4),X3))), inference(spm,[status(thm)],[c_0_41, c_0_40])).
% 13.27/13.47  cnf(c_0_45, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_43])).
% 13.27/13.47  fof(c_0_46, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 13.27/13.47  fof(c_0_47, plain, ![X26]:r1_tarski(k1_xboole_0,X26), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 13.27/13.47  cnf(c_0_48, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(k3_tarski(k2_tarski(X2,X3)),X3))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 13.27/13.47  cnf(c_0_49, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 13.27/13.47  cnf(c_0_50, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 13.27/13.47  cnf(c_0_51, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(k3_tarski(k2_tarski(X2,X3)),k4_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_48, c_0_42])).
% 13.27/13.47  cnf(c_0_52, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 13.27/13.47  fof(c_0_53, plain, ![X34, X35, X36]:(~r1_tarski(k4_xboole_0(X34,X35),X36)|r1_tarski(X34,k2_xboole_0(X35,X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 13.27/13.47  fof(c_0_54, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t31_relat_1])).
% 13.27/13.47  fof(c_0_55, plain, ![X11, X12, X14, X15, X16]:(((r2_hidden(esk2_2(X11,X12),X11)|r1_xboole_0(X11,X12))&(r2_hidden(esk2_2(X11,X12),X12)|r1_xboole_0(X11,X12)))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|~r1_xboole_0(X14,X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 13.27/13.47  fof(c_0_56, plain, ![X37]:r1_xboole_0(X37,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 13.27/13.47  fof(c_0_57, plain, ![X70]:(~v1_relat_1(X70)|k3_relat_1(X70)=k2_xboole_0(k1_relat_1(X70),k2_relat_1(X70))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 13.27/13.47  cnf(c_0_58, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(k3_tarski(k2_tarski(X2,X3)),k4_xboole_0(k4_xboole_0(X3,X2),X2)))), inference(spm,[status(thm)],[c_0_51, c_0_42])).
% 13.27/13.47  cnf(c_0_59, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_37]), c_0_39])).
% 13.27/13.47  cnf(c_0_60, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 13.27/13.47  fof(c_0_61, negated_conjecture, (v1_relat_1(esk8_0)&(v1_relat_1(esk9_0)&(r1_tarski(esk8_0,esk9_0)&~r1_tarski(k3_relat_1(esk8_0),k3_relat_1(esk9_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_54])])])).
% 13.27/13.47  cnf(c_0_62, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 13.27/13.47  cnf(c_0_63, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 13.27/13.47  fof(c_0_64, plain, ![X53, X54, X56]:((r2_hidden(esk4_2(X53,X54),X54)|~r2_hidden(X53,X54))&(~r2_hidden(X56,X54)|~r2_hidden(X56,esk4_2(X53,X54))|~r2_hidden(X53,X54))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).
% 13.27/13.47  fof(c_0_65, plain, ![X40, X41, X42]:(~r1_tarski(X40,X41)|~r1_tarski(X42,X41)|r1_tarski(k2_xboole_0(X40,X42),X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 13.27/13.47  cnf(c_0_66, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 13.27/13.47  cnf(c_0_67, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_tarski(k2_tarski(X2,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_45])).
% 13.27/13.47  cnf(c_0_68, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_60, c_0_27])).
% 13.27/13.47  cnf(c_0_69, negated_conjecture, (r1_tarski(esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 13.27/13.47  cnf(c_0_70, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 13.27/13.47  fof(c_0_71, plain, ![X38, X39]:r1_tarski(X38,k2_xboole_0(X38,X39)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 13.27/13.47  cnf(c_0_72, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 13.27/13.47  cnf(c_0_73, plain, (r2_hidden(esk4_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 13.27/13.47  fof(c_0_74, plain, ![X47, X49, X50, X51, X52]:(((r2_hidden(X47,esk3_1(X47))&(~r2_hidden(X49,esk3_1(X47))|~r1_tarski(X50,X49)|r2_hidden(X50,esk3_1(X47))))&(~r2_hidden(X51,esk3_1(X47))|r2_hidden(k1_zfmisc_1(X51),esk3_1(X47))))&(~r1_tarski(X52,esk3_1(X47))|r2_tarski(X52,esk3_1(X47))|r2_hidden(X52,esk3_1(X47)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t136_zfmisc_1])])])])])).
% 13.27/13.47  cnf(c_0_75, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 13.27/13.47  cnf(c_0_76, plain, (k3_relat_1(X1)=k3_tarski(k2_tarski(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_66, c_0_27])).
% 13.27/13.47  fof(c_0_77, plain, ![X19, X20, X21]:(~r1_tarski(X19,X20)|r1_tarski(X19,k2_xboole_0(X21,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 13.27/13.47  fof(c_0_78, plain, ![X71, X72]:(~v1_relat_1(X71)|(~v1_relat_1(X72)|k1_relat_1(k2_xboole_0(X71,X72))=k2_xboole_0(k1_relat_1(X71),k1_relat_1(X72)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relat_1])])])).
% 13.27/13.47  cnf(c_0_79, plain, (r1_tarski(X1,X2)|~r1_tarski(k4_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 13.27/13.47  cnf(c_0_80, negated_conjecture, (r1_tarski(X1,esk9_0)|~r1_tarski(X1,esk8_0)), inference(spm,[status(thm)],[c_0_36, c_0_69])).
% 13.27/13.47  cnf(c_0_81, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_70])).
% 13.27/13.47  cnf(c_0_82, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 13.27/13.47  cnf(c_0_83, plain, (~r2_hidden(esk4_2(X1,k1_xboole_0),X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 13.27/13.47  cnf(c_0_84, plain, (r2_hidden(X1,esk3_1(X1))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 13.27/13.47  fof(c_0_85, plain, ![X59, X60, X61, X63, X64, X65, X66, X68]:(((~r2_hidden(X61,X60)|r2_hidden(k4_tarski(esk5_3(X59,X60,X61),X61),X59)|X60!=k2_relat_1(X59))&(~r2_hidden(k4_tarski(X64,X63),X59)|r2_hidden(X63,X60)|X60!=k2_relat_1(X59)))&((~r2_hidden(esk6_2(X65,X66),X66)|~r2_hidden(k4_tarski(X68,esk6_2(X65,X66)),X65)|X66=k2_relat_1(X65))&(r2_hidden(esk6_2(X65,X66),X66)|r2_hidden(k4_tarski(esk7_2(X65,X66),esk6_2(X65,X66)),X65)|X66=k2_relat_1(X65)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 13.27/13.47  cnf(c_0_86, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_75, c_0_27])).
% 13.27/13.47  cnf(c_0_87, plain, (k3_tarski(k2_tarski(k2_relat_1(X1),k1_relat_1(X1)))=k3_relat_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_76, c_0_40])).
% 13.27/13.47  cnf(c_0_88, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 13.27/13.47  cnf(c_0_89, plain, (k1_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 13.27/13.47  cnf(c_0_90, negated_conjecture, (r1_tarski(X1,esk9_0)|~r1_tarski(k4_xboole_0(X1,esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 13.27/13.47  cnf(c_0_91, plain, (r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1),X2)), inference(spm,[status(thm)],[c_0_31, c_0_81])).
% 13.27/13.47  cnf(c_0_92, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_82, c_0_27])).
% 13.27/13.47  cnf(c_0_93, negated_conjecture, (r1_tarski(X1,esk9_0)|~r1_tarski(X2,esk8_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_36, c_0_80])).
% 13.27/13.47  cnf(c_0_94, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 13.27/13.47  cnf(c_0_95, plain, (r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 13.27/13.47  cnf(c_0_96, negated_conjecture, (~r1_tarski(k3_relat_1(esk8_0),k3_relat_1(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 13.27/13.47  cnf(c_0_97, plain, (r1_tarski(k3_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 13.27/13.47  cnf(c_0_98, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 13.27/13.47  cnf(c_0_99, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_88, c_0_27])).
% 13.27/13.47  cnf(c_0_100, plain, (k1_relat_1(k3_tarski(k2_tarski(X1,X2)))=k3_tarski(k2_tarski(k1_relat_1(X1),k1_relat_1(X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_27]), c_0_27])).
% 13.27/13.47  cnf(c_0_101, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk8_0,esk9_0)),esk9_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_40])).
% 13.27/13.47  cnf(c_0_102, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_92, c_0_40])).
% 13.27/13.47  fof(c_0_103, plain, ![X73, X74]:(~v1_relat_1(X73)|(~v1_relat_1(X74)|r1_tarski(k6_subset_1(k2_relat_1(X73),k2_relat_1(X74)),k2_relat_1(k6_subset_1(X73,X74))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_relat_1])])])).
% 13.27/13.47  fof(c_0_104, plain, ![X57, X58]:k6_subset_1(X57,X58)=k4_xboole_0(X57,X58), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 13.27/13.47  cnf(c_0_105, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))), inference(spm,[status(thm)],[c_0_31, c_0_40])).
% 13.27/13.47  cnf(c_0_106, negated_conjecture, (r1_tarski(X1,esk9_0)|~r1_tarski(X1,k4_xboole_0(esk8_0,X2))), inference(spm,[status(thm)],[c_0_93, c_0_32])).
% 13.27/13.47  cnf(c_0_107, plain, (X1!=k2_relat_1(k1_xboole_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 13.27/13.47  fof(c_0_108, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 13.27/13.47  cnf(c_0_109, negated_conjecture, (~r1_tarski(k1_relat_1(esk8_0),k3_relat_1(esk9_0))|~r1_tarski(k2_relat_1(esk8_0),k3_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98])])).
% 13.27/13.47  cnf(c_0_110, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_99, c_0_87])).
% 13.27/13.47  cnf(c_0_111, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 13.27/13.47  cnf(c_0_112, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(k3_tarski(k2_tarski(X1,X2))))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_92, c_0_100])).
% 13.27/13.47  cnf(c_0_113, negated_conjecture, (k3_tarski(k2_tarski(esk8_0,esk9_0))=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_101]), c_0_102])])).
% 13.27/13.47  cnf(c_0_114, plain, (r1_tarski(k6_subset_1(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k6_subset_1(X1,X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 13.27/13.47  cnf(c_0_115, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_104])).
% 13.27/13.47  cnf(c_0_116, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(k4_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_105, c_0_68])).
% 13.27/13.47  cnf(c_0_117, negated_conjecture, (r1_tarski(k4_xboole_0(esk8_0,X1),esk9_0)), inference(spm,[status(thm)],[c_0_106, c_0_81])).
% 13.27/13.47  cnf(c_0_118, plain, (~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(er,[status(thm)],[c_0_107])).
% 13.27/13.47  cnf(c_0_119, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_108])).
% 13.27/13.47  cnf(c_0_120, negated_conjecture, (~r1_tarski(k2_relat_1(esk8_0),k3_relat_1(esk9_0))|~r1_tarski(k1_relat_1(esk8_0),k1_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_111])])).
% 13.27/13.47  cnf(c_0_121, negated_conjecture, (r1_tarski(k1_relat_1(esk8_0),k1_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_111]), c_0_98])])).
% 13.27/13.47  cnf(c_0_122, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_36, c_0_92])).
% 13.27/13.47  cnf(c_0_123, plain, (r1_tarski(k4_xboole_0(k2_relat_1(X1),k2_relat_1(X2)),k2_relat_1(k4_xboole_0(X1,X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_115]), c_0_115])).
% 13.27/13.47  cnf(c_0_124, negated_conjecture, (r1_tarski(k4_xboole_0(esk8_0,esk9_0),X1)), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 13.27/13.47  cnf(c_0_125, plain, (r1_tarski(k2_relat_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 13.27/13.47  cnf(c_0_126, negated_conjecture, (~r1_tarski(k2_relat_1(esk8_0),k3_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_121])])).
% 13.27/13.47  cnf(c_0_127, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_122, c_0_87])).
% 13.27/13.47  cnf(c_0_128, plain, (r1_tarski(k4_xboole_0(k2_relat_1(X1),k2_relat_1(k4_xboole_0(X1,X2))),k2_relat_1(X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_116, c_0_123])).
% 13.27/13.47  cnf(c_0_129, negated_conjecture, (k4_xboole_0(esk8_0,esk9_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_124])).
% 13.27/13.47  cnf(c_0_130, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_125])).
% 13.27/13.47  cnf(c_0_131, negated_conjecture, (~r1_tarski(k2_relat_1(esk8_0),k2_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_111])])).
% 13.27/13.47  cnf(c_0_132, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_130]), c_0_45]), c_0_111]), c_0_98])]), c_0_131]), ['proof']).
% 13.27/13.47  # SZS output end CNFRefutation
% 13.27/13.47  # Proof object total steps             : 133
% 13.27/13.47  # Proof object clause steps            : 84
% 13.27/13.47  # Proof object formula steps           : 49
% 13.27/13.47  # Proof object conjectures             : 22
% 13.27/13.47  # Proof object clause conjectures      : 19
% 13.27/13.47  # Proof object formula conjectures     : 3
% 13.27/13.47  # Proof object initial clauses used    : 28
% 13.27/13.47  # Proof object initial formulas used   : 24
% 13.27/13.47  # Proof object generating inferences   : 43
% 13.27/13.47  # Proof object simplifying inferences  : 38
% 13.27/13.47  # Training examples: 0 positive, 0 negative
% 13.27/13.47  # Parsed axioms                        : 24
% 13.27/13.47  # Removed by relevancy pruning/SinE    : 0
% 13.27/13.47  # Initial clauses                      : 40
% 13.27/13.47  # Removed in clause preprocessing      : 2
% 13.27/13.47  # Initial clauses in saturation        : 38
% 13.27/13.47  # Processed clauses                    : 23387
% 13.27/13.47  # ...of these trivial                  : 462
% 13.27/13.47  # ...subsumed                          : 18302
% 13.27/13.47  # ...remaining for further processing  : 4623
% 13.27/13.47  # Other redundant clauses eliminated   : 2
% 13.27/13.47  # Clauses deleted for lack of memory   : 0
% 13.27/13.47  # Backward-subsumed                    : 192
% 13.27/13.47  # Backward-rewritten                   : 54
% 13.27/13.47  # Generated clauses                    : 848574
% 13.27/13.47  # ...of the previous two non-trivial   : 807152
% 13.27/13.47  # Contextual simplify-reflections      : 41
% 13.27/13.47  # Paramodulations                      : 848495
% 13.27/13.47  # Factorizations                       : 8
% 13.27/13.47  # Equation resolutions                 : 70
% 13.27/13.47  # Propositional unsat checks           : 0
% 13.27/13.47  #    Propositional check models        : 0
% 13.27/13.47  #    Propositional check unsatisfiable : 0
% 13.27/13.47  #    Propositional clauses             : 0
% 13.27/13.47  #    Propositional clauses after purity: 0
% 13.27/13.47  #    Propositional unsat core size     : 0
% 13.27/13.47  #    Propositional preprocessing time  : 0.000
% 13.27/13.47  #    Propositional encoding time       : 0.000
% 13.27/13.47  #    Propositional solver time         : 0.000
% 13.27/13.47  #    Success case prop preproc time    : 0.000
% 13.27/13.47  #    Success case prop encoding time   : 0.000
% 13.27/13.47  #    Success case prop solver time     : 0.000
% 13.27/13.47  # Current number of processed clauses  : 4374
% 13.27/13.47  #    Positive orientable unit clauses  : 232
% 13.27/13.47  #    Positive unorientable unit clauses: 1
% 13.27/13.47  #    Negative unit clauses             : 29
% 13.27/13.47  #    Non-unit-clauses                  : 4112
% 13.27/13.47  # Current number of unprocessed clauses: 782388
% 13.27/13.47  # ...number of literals in the above   : 4075679
% 13.27/13.47  # Current number of archived formulas  : 0
% 13.27/13.47  # Current number of archived clauses   : 249
% 13.27/13.47  # Clause-clause subsumption calls (NU) : 3623474
% 13.27/13.47  # Rec. Clause-clause subsumption calls : 1145919
% 13.27/13.47  # Non-unit clause-clause subsumptions  : 11671
% 13.27/13.47  # Unit Clause-clause subsumption calls : 18452
% 13.27/13.47  # Rewrite failures with RHS unbound    : 0
% 13.27/13.47  # BW rewrite match attempts            : 8990
% 13.27/13.47  # BW rewrite match successes           : 20
% 13.27/13.47  # Condensation attempts                : 0
% 13.27/13.47  # Condensation successes               : 0
% 13.27/13.47  # Termbank termtop insertions          : 16221321
% 13.27/13.51  
% 13.27/13.51  # -------------------------------------------------
% 13.27/13.51  # User time                : 12.745 s
% 13.27/13.51  # System time              : 0.424 s
% 13.27/13.51  # Total time               : 13.168 s
% 13.27/13.51  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
