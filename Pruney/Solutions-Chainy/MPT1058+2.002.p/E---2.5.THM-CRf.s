%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:26 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 391 expanded)
%              Number of clauses        :   66 ( 154 expanded)
%              Number of leaves         :   29 ( 111 expanded)
%              Depth                    :   17
%              Number of atoms          :  297 ( 716 expanded)
%              Number of equality atoms :   74 ( 320 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d13_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( r2_hidden(X4,k1_relat_1(X1))
                & r2_hidden(k1_funct_1(X1,X4),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t49_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_tarski(X1,k3_zfmisc_1(X1,X2,X3))
          & ~ r1_tarski(X1,k3_zfmisc_1(X2,X3,X1))
          & ~ r1_tarski(X1,k3_zfmisc_1(X3,X1,X2)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t175_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( r1_tarski(k10_relat_1(X1,X3),X2)
         => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t175_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(t162_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(c_0_29,plain,(
    ! [X75,X76,X77,X78,X79,X80,X81] :
      ( ( r2_hidden(X78,k1_relat_1(X75))
        | ~ r2_hidden(X78,X77)
        | X77 != k10_relat_1(X75,X76)
        | ~ v1_relat_1(X75)
        | ~ v1_funct_1(X75) )
      & ( r2_hidden(k1_funct_1(X75,X78),X76)
        | ~ r2_hidden(X78,X77)
        | X77 != k10_relat_1(X75,X76)
        | ~ v1_relat_1(X75)
        | ~ v1_funct_1(X75) )
      & ( ~ r2_hidden(X79,k1_relat_1(X75))
        | ~ r2_hidden(k1_funct_1(X75,X79),X76)
        | r2_hidden(X79,X77)
        | X77 != k10_relat_1(X75,X76)
        | ~ v1_relat_1(X75)
        | ~ v1_funct_1(X75) )
      & ( ~ r2_hidden(esk2_3(X75,X80,X81),X81)
        | ~ r2_hidden(esk2_3(X75,X80,X81),k1_relat_1(X75))
        | ~ r2_hidden(k1_funct_1(X75,esk2_3(X75,X80,X81)),X80)
        | X81 = k10_relat_1(X75,X80)
        | ~ v1_relat_1(X75)
        | ~ v1_funct_1(X75) )
      & ( r2_hidden(esk2_3(X75,X80,X81),k1_relat_1(X75))
        | r2_hidden(esk2_3(X75,X80,X81),X81)
        | X81 = k10_relat_1(X75,X80)
        | ~ v1_relat_1(X75)
        | ~ v1_funct_1(X75) )
      & ( r2_hidden(k1_funct_1(X75,esk2_3(X75,X80,X81)),X80)
        | r2_hidden(esk2_3(X75,X80,X81),X81)
        | X81 = k10_relat_1(X75,X80)
        | ~ v1_relat_1(X75)
        | ~ v1_funct_1(X75) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).

fof(c_0_30,plain,(
    ! [X93,X94] :
      ( ~ r2_hidden(X93,X94)
      | ~ r1_tarski(X94,X93) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_31,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X4 != k10_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_33,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3)) ),
    inference(er,[status(thm)],[c_0_31])).

fof(c_0_34,plain,(
    ! [X28] : r1_tarski(k1_xboole_0,X28) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_35,plain,(
    ! [X98,X99,X100] :
      ( ( ~ r1_tarski(X98,k3_zfmisc_1(X98,X99,X100))
        | X98 = k1_xboole_0 )
      & ( ~ r1_tarski(X98,k3_zfmisc_1(X99,X100,X98))
        | X98 = k1_xboole_0 )
      & ( ~ r1_tarski(X98,k3_zfmisc_1(X100,X98,X99))
        | X98 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_mcart_1])])])])).

fof(c_0_36,plain,(
    ! [X95,X96,X97] : k3_zfmisc_1(X95,X96,X97) = k2_zfmisc_1(k2_zfmisc_1(X95,X96),X97) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_37,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ r1_tarski(X3,k1_funct_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_39,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk1_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk1_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_44,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2,X3] :
            ( r1_tarski(k10_relat_1(X1,X3),X2)
           => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t175_funct_2])).

fof(c_0_45,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(k2_xboole_0(X18,X19),X20)
      | r1_tarski(X18,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_46,plain,(
    ! [X21,X22] :
      ( ~ r1_tarski(X21,X22)
      | k2_xboole_0(X21,X22) = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_47,plain,(
    ! [X58,X59] : k1_setfam_1(k2_tarski(X58,X59)) = k3_xboole_0(X58,X59) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_48,plain,(
    ! [X31,X32] : k1_enumset1(X31,X31,X32) = k2_tarski(X31,X32) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,plain,
    ( r1_tarski(k10_relat_1(X1,k1_xboole_0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_51,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r1_tarski(k10_relat_1(esk3_0,esk5_0),esk4_0)
    & k10_relat_1(esk3_0,esk5_0) != k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_54,plain,(
    ! [X23,X24] : r1_tarski(k3_xboole_0(X23,X24),X23) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_55,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_57,plain,(
    ! [X33,X34,X35] : k2_enumset1(X33,X33,X34,X35) = k1_enumset1(X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_58,plain,(
    ! [X36,X37,X38,X39] : k3_enumset1(X36,X36,X37,X38,X39) = k2_enumset1(X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_59,plain,(
    ! [X40,X41,X42,X43,X44] : k4_enumset1(X40,X40,X41,X42,X43,X44) = k3_enumset1(X40,X41,X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_60,plain,(
    ! [X45,X46,X47,X48,X49,X50] : k5_enumset1(X45,X45,X46,X47,X48,X49,X50) = k4_enumset1(X45,X46,X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_61,plain,(
    ! [X51,X52,X53,X54,X55,X56,X57] : k6_enumset1(X51,X51,X52,X53,X54,X55,X56,X57) = k5_enumset1(X51,X52,X53,X54,X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_62,plain,(
    ! [X85,X86,X87] :
      ( ~ v1_relat_1(X87)
      | k10_relat_1(k7_relat_1(X87,X85),X86) = k3_xboole_0(X85,k10_relat_1(X87,X86)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

fof(c_0_63,plain,(
    ! [X29,X30] : k2_tarski(X29,X30) = k2_tarski(X30,X29) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_64,plain,(
    ! [X67,X68,X69] :
      ( ~ v1_relat_1(X69)
      | k10_relat_1(X69,k2_xboole_0(X67,X68)) = k2_xboole_0(k10_relat_1(X69,X67),k10_relat_1(X69,X68)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).

cnf(c_0_65,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_67,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_68,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_71,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_72,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_73,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_74,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_75,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_76,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_77,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_78,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_79,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_80,plain,
    ( k10_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_81,negated_conjecture,
    ( k10_relat_1(esk3_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_82,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

fof(c_0_83,plain,(
    ! [X88,X89] :
      ( ~ v1_relat_1(X89)
      | ~ v1_funct_1(X89)
      | r1_tarski(k9_relat_1(X89,k10_relat_1(X89,X88)),X88) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

fof(c_0_84,plain,(
    ! [X62,X63,X64] :
      ( ~ v1_relat_1(X62)
      | ~ r1_tarski(X63,X64)
      | k9_relat_1(k7_relat_1(X62,X64),X63) = k9_relat_1(X62,X63) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).

fof(c_0_85,plain,(
    ! [X60,X61] :
      ( ~ v1_relat_1(X60)
      | v1_relat_1(k7_relat_1(X60,X61)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,k10_relat_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_87,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_74]),c_0_75]),c_0_76]),c_0_77])).

cnf(c_0_88,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_72]),c_0_73]),c_0_74]),c_0_75]),c_0_76]),c_0_77])).

cnf(c_0_89,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_56]),c_0_56]),c_0_73]),c_0_73]),c_0_74]),c_0_74]),c_0_75]),c_0_75]),c_0_76]),c_0_76]),c_0_77]),c_0_77])).

fof(c_0_90,plain,(
    ! [X65,X66] :
      ( ~ v1_relat_1(X66)
      | r1_tarski(k10_relat_1(X66,X65),k1_relat_1(X66)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

cnf(c_0_91,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k10_relat_1(esk3_0,X1)) = k10_relat_1(esk3_0,k2_xboole_0(X1,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_67])]),c_0_82])).

cnf(c_0_92,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_93,plain,
    ( k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_94,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(k1_setfam_1(k6_enumset1(k10_relat_1(esk3_0,esk5_0),k10_relat_1(esk3_0,esk5_0),k10_relat_1(esk3_0,esk5_0),k10_relat_1(esk3_0,esk5_0),k10_relat_1(esk3_0,esk5_0),k10_relat_1(esk3_0,esk5_0),k10_relat_1(esk3_0,esk5_0),X1)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_96,plain,
    ( k1_setfam_1(k6_enumset1(k10_relat_1(X1,X2),k10_relat_1(X1,X2),k10_relat_1(X1,X2),k10_relat_1(X1,X2),k10_relat_1(X1,X2),k10_relat_1(X1,X2),k10_relat_1(X1,X2),X3)) = k10_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_97,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_98,negated_conjecture,
    ( k10_relat_1(esk3_0,k2_xboole_0(X1,k1_xboole_0)) = k10_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_91]),c_0_38])])).

fof(c_0_99,plain,(
    ! [X90,X91,X92] :
      ( ~ v1_relat_1(X92)
      | ~ v1_funct_1(X92)
      | ~ r1_tarski(X90,k1_relat_1(X92))
      | ~ r1_tarski(k9_relat_1(X92,X90),X91)
      | r1_tarski(X90,k10_relat_1(X92,X91)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

cnf(c_0_100,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(k7_relat_1(X1,X2),X3)),X3)
    | ~ v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(k7_relat_1(X1,X2),X3),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk3_0,X1),esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_67])])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,X1),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_67])])).

cnf(c_0_103,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_87,c_0_89])).

cnf(c_0_104,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0)),esk5_0)
    | ~ v1_funct_1(k7_relat_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_67])])).

cnf(c_0_106,negated_conjecture,
    ( r1_tarski(X1,k1_relat_1(esk3_0))
    | ~ r1_tarski(X1,k10_relat_1(esk3_0,X2)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_102])).

cnf(c_0_107,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(X1,X2),X3),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_88])).

fof(c_0_108,plain,(
    ! [X25,X26,X27] :
      ( ~ r1_tarski(X25,X26)
      | ~ r1_tarski(X25,X27)
      | r1_tarski(X25,k3_xboole_0(X26,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_109,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0),k10_relat_1(esk3_0,esk5_0))
    | ~ v1_funct_1(k7_relat_1(esk3_0,esk4_0))
    | ~ r1_tarski(k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_66]),c_0_67])])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk3_0,X1),X2),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_67])])).

cnf(c_0_112,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_113,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0),k10_relat_1(esk3_0,esk5_0))
    | ~ v1_funct_1(k7_relat_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_111])])).

cnf(c_0_115,negated_conjecture,
    ( k10_relat_1(esk3_0,esk5_0) != k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_116,plain,
    ( r1_tarski(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_72]),c_0_73]),c_0_74]),c_0_75]),c_0_76]),c_0_77])).

cnf(c_0_117,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_118,negated_conjecture,
    ( ~ v1_funct_1(k7_relat_1(esk3_0,esk4_0))
    | ~ r1_tarski(k10_relat_1(esk3_0,esk5_0),k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115])).

cnf(c_0_119,plain,
    ( r1_tarski(X1,k10_relat_1(k7_relat_1(X2,X3),X4))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k10_relat_1(X2,X4))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_116,c_0_88])).

cnf(c_0_120,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_117])).

fof(c_0_121,plain,(
    ! [X83,X84] :
      ( ( v1_relat_1(k7_relat_1(X83,X84))
        | ~ v1_relat_1(X83)
        | ~ v1_funct_1(X83) )
      & ( v1_funct_1(k7_relat_1(X83,X84))
        | ~ v1_relat_1(X83)
        | ~ v1_funct_1(X83) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

cnf(c_0_122,negated_conjecture,
    ( ~ v1_funct_1(k7_relat_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_67]),c_0_120]),c_0_70])])).

cnf(c_0_123,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_121])).

cnf(c_0_124,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_66]),c_0_67])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:07:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.48/0.65  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.48/0.65  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.48/0.65  #
% 0.48/0.65  # Preprocessing time       : 0.030 s
% 0.48/0.65  # Presaturation interreduction done
% 0.48/0.65  
% 0.48/0.65  # Proof found!
% 0.48/0.65  # SZS status Theorem
% 0.48/0.65  # SZS output start CNFRefutation
% 0.48/0.65  fof(d13_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,k1_relat_1(X1))&r2_hidden(k1_funct_1(X1,X4),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 0.48/0.65  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.48/0.65  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.48/0.65  fof(t49_mcart_1, axiom, ![X1, X2, X3]:(~(((~(r1_tarski(X1,k3_zfmisc_1(X1,X2,X3)))&~(r1_tarski(X1,k3_zfmisc_1(X2,X3,X1))))&~(r1_tarski(X1,k3_zfmisc_1(X3,X1,X2)))))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_mcart_1)).
% 0.48/0.65  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.48/0.65  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.48/0.65  fof(t175_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 0.48/0.65  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.48/0.65  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.48/0.65  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.48/0.65  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.48/0.65  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.48/0.65  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.48/0.65  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.48/0.65  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.48/0.65  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.48/0.65  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.48/0.65  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 0.48/0.65  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.48/0.65  fof(t175_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 0.48/0.65  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.48/0.65  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 0.48/0.65  fof(t162_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 0.48/0.65  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.48/0.65  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 0.48/0.65  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 0.48/0.65  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.48/0.65  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.48/0.65  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.48/0.65  fof(c_0_29, plain, ![X75, X76, X77, X78, X79, X80, X81]:((((r2_hidden(X78,k1_relat_1(X75))|~r2_hidden(X78,X77)|X77!=k10_relat_1(X75,X76)|(~v1_relat_1(X75)|~v1_funct_1(X75)))&(r2_hidden(k1_funct_1(X75,X78),X76)|~r2_hidden(X78,X77)|X77!=k10_relat_1(X75,X76)|(~v1_relat_1(X75)|~v1_funct_1(X75))))&(~r2_hidden(X79,k1_relat_1(X75))|~r2_hidden(k1_funct_1(X75,X79),X76)|r2_hidden(X79,X77)|X77!=k10_relat_1(X75,X76)|(~v1_relat_1(X75)|~v1_funct_1(X75))))&((~r2_hidden(esk2_3(X75,X80,X81),X81)|(~r2_hidden(esk2_3(X75,X80,X81),k1_relat_1(X75))|~r2_hidden(k1_funct_1(X75,esk2_3(X75,X80,X81)),X80))|X81=k10_relat_1(X75,X80)|(~v1_relat_1(X75)|~v1_funct_1(X75)))&((r2_hidden(esk2_3(X75,X80,X81),k1_relat_1(X75))|r2_hidden(esk2_3(X75,X80,X81),X81)|X81=k10_relat_1(X75,X80)|(~v1_relat_1(X75)|~v1_funct_1(X75)))&(r2_hidden(k1_funct_1(X75,esk2_3(X75,X80,X81)),X80)|r2_hidden(esk2_3(X75,X80,X81),X81)|X81=k10_relat_1(X75,X80)|(~v1_relat_1(X75)|~v1_funct_1(X75)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).
% 0.48/0.65  fof(c_0_30, plain, ![X93, X94]:(~r2_hidden(X93,X94)|~r1_tarski(X94,X93)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.48/0.65  cnf(c_0_31, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~r2_hidden(X2,X4)|X4!=k10_relat_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.48/0.65  cnf(c_0_32, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.48/0.65  cnf(c_0_33, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,X3))), inference(er,[status(thm)],[c_0_31])).
% 0.48/0.65  fof(c_0_34, plain, ![X28]:r1_tarski(k1_xboole_0,X28), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.48/0.65  fof(c_0_35, plain, ![X98, X99, X100]:(((~r1_tarski(X98,k3_zfmisc_1(X98,X99,X100))|X98=k1_xboole_0)&(~r1_tarski(X98,k3_zfmisc_1(X99,X100,X98))|X98=k1_xboole_0))&(~r1_tarski(X98,k3_zfmisc_1(X100,X98,X99))|X98=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_mcart_1])])])])).
% 0.48/0.65  fof(c_0_36, plain, ![X95, X96, X97]:k3_zfmisc_1(X95,X96,X97)=k2_zfmisc_1(k2_zfmisc_1(X95,X96),X97), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.48/0.65  cnf(c_0_37, plain, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,X3))|~r1_tarski(X3,k1_funct_1(X1,X2))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.48/0.65  cnf(c_0_38, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.48/0.65  fof(c_0_39, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk1_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk1_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.48/0.65  cnf(c_0_40, plain, (X1=k1_xboole_0|~r1_tarski(X1,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.48/0.65  cnf(c_0_41, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.48/0.65  cnf(c_0_42, plain, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.48/0.65  cnf(c_0_43, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.48/0.65  fof(c_0_44, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3)))), inference(assume_negation,[status(cth)],[t175_funct_2])).
% 0.48/0.65  fof(c_0_45, plain, ![X18, X19, X20]:(~r1_tarski(k2_xboole_0(X18,X19),X20)|r1_tarski(X18,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.48/0.65  fof(c_0_46, plain, ![X21, X22]:(~r1_tarski(X21,X22)|k2_xboole_0(X21,X22)=X22), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.48/0.65  fof(c_0_47, plain, ![X58, X59]:k1_setfam_1(k2_tarski(X58,X59))=k3_xboole_0(X58,X59), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.48/0.65  fof(c_0_48, plain, ![X31, X32]:k1_enumset1(X31,X31,X32)=k2_tarski(X31,X32), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.48/0.65  cnf(c_0_49, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.48/0.65  cnf(c_0_50, plain, (r1_tarski(k10_relat_1(X1,k1_xboole_0),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.48/0.65  fof(c_0_51, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(r1_tarski(k10_relat_1(esk3_0,esk5_0),esk4_0)&k10_relat_1(esk3_0,esk5_0)!=k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])).
% 0.48/0.65  cnf(c_0_52, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.48/0.65  cnf(c_0_53, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.48/0.65  fof(c_0_54, plain, ![X23, X24]:r1_tarski(k3_xboole_0(X23,X24),X23), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.48/0.65  cnf(c_0_55, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.48/0.65  cnf(c_0_56, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.48/0.65  fof(c_0_57, plain, ![X33, X34, X35]:k2_enumset1(X33,X33,X34,X35)=k1_enumset1(X33,X34,X35), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.48/0.65  fof(c_0_58, plain, ![X36, X37, X38, X39]:k3_enumset1(X36,X36,X37,X38,X39)=k2_enumset1(X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.48/0.65  fof(c_0_59, plain, ![X40, X41, X42, X43, X44]:k4_enumset1(X40,X40,X41,X42,X43,X44)=k3_enumset1(X40,X41,X42,X43,X44), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.48/0.65  fof(c_0_60, plain, ![X45, X46, X47, X48, X49, X50]:k5_enumset1(X45,X45,X46,X47,X48,X49,X50)=k4_enumset1(X45,X46,X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.48/0.65  fof(c_0_61, plain, ![X51, X52, X53, X54, X55, X56, X57]:k6_enumset1(X51,X51,X52,X53,X54,X55,X56,X57)=k5_enumset1(X51,X52,X53,X54,X55,X56,X57), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.48/0.65  fof(c_0_62, plain, ![X85, X86, X87]:(~v1_relat_1(X87)|k10_relat_1(k7_relat_1(X87,X85),X86)=k3_xboole_0(X85,k10_relat_1(X87,X86))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.48/0.65  fof(c_0_63, plain, ![X29, X30]:k2_tarski(X29,X30)=k2_tarski(X30,X29), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.48/0.65  fof(c_0_64, plain, ![X67, X68, X69]:(~v1_relat_1(X69)|k10_relat_1(X69,k2_xboole_0(X67,X68))=k2_xboole_0(k10_relat_1(X69,X67),k10_relat_1(X69,X68))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).
% 0.48/0.65  cnf(c_0_65, plain, (k10_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.48/0.65  cnf(c_0_66, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.48/0.65  cnf(c_0_67, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.48/0.65  fof(c_0_68, plain, ![X8, X9]:k2_xboole_0(X8,X9)=k2_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.48/0.65  cnf(c_0_69, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.48/0.65  cnf(c_0_70, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.48/0.65  cnf(c_0_71, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.48/0.65  cnf(c_0_72, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.48/0.65  cnf(c_0_73, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.48/0.65  cnf(c_0_74, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.48/0.65  cnf(c_0_75, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.48/0.65  cnf(c_0_76, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.48/0.65  cnf(c_0_77, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.48/0.65  cnf(c_0_78, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.48/0.65  cnf(c_0_79, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.48/0.65  cnf(c_0_80, plain, (k10_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.48/0.65  cnf(c_0_81, negated_conjecture, (k10_relat_1(esk3_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])])).
% 0.48/0.65  cnf(c_0_82, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.48/0.65  fof(c_0_83, plain, ![X88, X89]:(~v1_relat_1(X89)|~v1_funct_1(X89)|r1_tarski(k9_relat_1(X89,k10_relat_1(X89,X88)),X88)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.48/0.65  fof(c_0_84, plain, ![X62, X63, X64]:(~v1_relat_1(X62)|(~r1_tarski(X63,X64)|k9_relat_1(k7_relat_1(X62,X64),X63)=k9_relat_1(X62,X63))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).
% 0.48/0.65  fof(c_0_85, plain, ![X60, X61]:(~v1_relat_1(X60)|v1_relat_1(k7_relat_1(X60,X61))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.48/0.65  cnf(c_0_86, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,k10_relat_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.48/0.65  cnf(c_0_87, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_74]), c_0_75]), c_0_76]), c_0_77])).
% 0.48/0.65  cnf(c_0_88, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_72]), c_0_73]), c_0_74]), c_0_75]), c_0_76]), c_0_77])).
% 0.48/0.65  cnf(c_0_89, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_56]), c_0_56]), c_0_73]), c_0_73]), c_0_74]), c_0_74]), c_0_75]), c_0_75]), c_0_76]), c_0_76]), c_0_77]), c_0_77])).
% 0.48/0.65  fof(c_0_90, plain, ![X65, X66]:(~v1_relat_1(X66)|r1_tarski(k10_relat_1(X66,X65),k1_relat_1(X66))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.48/0.65  cnf(c_0_91, negated_conjecture, (k2_xboole_0(k1_xboole_0,k10_relat_1(esk3_0,X1))=k10_relat_1(esk3_0,k2_xboole_0(X1,k1_xboole_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_67])]), c_0_82])).
% 0.48/0.65  cnf(c_0_92, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.48/0.65  cnf(c_0_93, plain, (k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.48/0.65  cnf(c_0_94, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.48/0.65  cnf(c_0_95, negated_conjecture, (r1_tarski(k1_setfam_1(k6_enumset1(k10_relat_1(esk3_0,esk5_0),k10_relat_1(esk3_0,esk5_0),k10_relat_1(esk3_0,esk5_0),k10_relat_1(esk3_0,esk5_0),k10_relat_1(esk3_0,esk5_0),k10_relat_1(esk3_0,esk5_0),k10_relat_1(esk3_0,esk5_0),X1)),esk4_0)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.48/0.65  cnf(c_0_96, plain, (k1_setfam_1(k6_enumset1(k10_relat_1(X1,X2),k10_relat_1(X1,X2),k10_relat_1(X1,X2),k10_relat_1(X1,X2),k10_relat_1(X1,X2),k10_relat_1(X1,X2),k10_relat_1(X1,X2),X3))=k10_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.48/0.65  cnf(c_0_97, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.48/0.65  cnf(c_0_98, negated_conjecture, (k10_relat_1(esk3_0,k2_xboole_0(X1,k1_xboole_0))=k10_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_91]), c_0_38])])).
% 0.48/0.65  fof(c_0_99, plain, ![X90, X91, X92]:(~v1_relat_1(X92)|~v1_funct_1(X92)|(~r1_tarski(X90,k1_relat_1(X92))|~r1_tarski(k9_relat_1(X92,X90),X91)|r1_tarski(X90,k10_relat_1(X92,X91)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 0.48/0.65  cnf(c_0_100, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(k7_relat_1(X1,X2),X3)),X3)|~v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(k7_relat_1(X1,X2),X3),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94])).
% 0.48/0.65  cnf(c_0_101, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk3_0,X1),esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_67])])).
% 0.48/0.65  cnf(c_0_102, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,X1),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_67])])).
% 0.48/0.65  cnf(c_0_103, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X2)), inference(spm,[status(thm)],[c_0_87, c_0_89])).
% 0.48/0.65  cnf(c_0_104, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.48/0.65  cnf(c_0_105, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0)),esk5_0)|~v1_funct_1(k7_relat_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_67])])).
% 0.48/0.65  cnf(c_0_106, negated_conjecture, (r1_tarski(X1,k1_relat_1(esk3_0))|~r1_tarski(X1,k10_relat_1(esk3_0,X2))), inference(spm,[status(thm)],[c_0_69, c_0_102])).
% 0.48/0.65  cnf(c_0_107, plain, (r1_tarski(k10_relat_1(k7_relat_1(X1,X2),X3),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_103, c_0_88])).
% 0.48/0.65  fof(c_0_108, plain, ![X25, X26, X27]:(~r1_tarski(X25,X26)|~r1_tarski(X25,X27)|r1_tarski(X25,k3_xboole_0(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.48/0.65  fof(c_0_109, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.48/0.65  cnf(c_0_110, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0),k10_relat_1(esk3_0,esk5_0))|~v1_funct_1(k7_relat_1(esk3_0,esk4_0))|~r1_tarski(k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_66]), c_0_67])])).
% 0.48/0.65  cnf(c_0_111, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk3_0,X1),X2),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_67])])).
% 0.48/0.65  cnf(c_0_112, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_108])).
% 0.48/0.65  cnf(c_0_113, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_109])).
% 0.48/0.65  cnf(c_0_114, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0),k10_relat_1(esk3_0,esk5_0))|~v1_funct_1(k7_relat_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_111])])).
% 0.48/0.65  cnf(c_0_115, negated_conjecture, (k10_relat_1(esk3_0,esk5_0)!=k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.48/0.65  cnf(c_0_116, plain, (r1_tarski(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_72]), c_0_73]), c_0_74]), c_0_75]), c_0_76]), c_0_77])).
% 0.48/0.65  cnf(c_0_117, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_109])).
% 0.48/0.65  cnf(c_0_118, negated_conjecture, (~v1_funct_1(k7_relat_1(esk3_0,esk4_0))|~r1_tarski(k10_relat_1(esk3_0,esk5_0),k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_115])).
% 0.48/0.65  cnf(c_0_119, plain, (r1_tarski(X1,k10_relat_1(k7_relat_1(X2,X3),X4))|~v1_relat_1(X2)|~r1_tarski(X1,k10_relat_1(X2,X4))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_116, c_0_88])).
% 0.48/0.65  cnf(c_0_120, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_117])).
% 0.48/0.65  fof(c_0_121, plain, ![X83, X84]:((v1_relat_1(k7_relat_1(X83,X84))|(~v1_relat_1(X83)|~v1_funct_1(X83)))&(v1_funct_1(k7_relat_1(X83,X84))|(~v1_relat_1(X83)|~v1_funct_1(X83)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.48/0.65  cnf(c_0_122, negated_conjecture, (~v1_funct_1(k7_relat_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_67]), c_0_120]), c_0_70])])).
% 0.48/0.65  cnf(c_0_123, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_121])).
% 0.48/0.65  cnf(c_0_124, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_66]), c_0_67])]), ['proof']).
% 0.48/0.65  # SZS output end CNFRefutation
% 0.48/0.65  # Proof object total steps             : 125
% 0.48/0.65  # Proof object clause steps            : 66
% 0.48/0.65  # Proof object formula steps           : 59
% 0.48/0.65  # Proof object conjectures             : 22
% 0.48/0.65  # Proof object clause conjectures      : 19
% 0.48/0.65  # Proof object formula conjectures     : 3
% 0.48/0.65  # Proof object initial clauses used    : 33
% 0.48/0.65  # Proof object initial formulas used   : 29
% 0.48/0.65  # Proof object generating inferences   : 24
% 0.48/0.65  # Proof object simplifying inferences  : 63
% 0.48/0.65  # Training examples: 0 positive, 0 negative
% 0.48/0.65  # Parsed axioms                        : 31
% 0.48/0.65  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.65  # Initial clauses                      : 46
% 0.48/0.65  # Removed in clause preprocessing      : 8
% 0.48/0.65  # Initial clauses in saturation        : 38
% 0.48/0.65  # Processed clauses                    : 2896
% 0.48/0.65  # ...of these trivial                  : 23
% 0.48/0.65  # ...subsumed                          : 2294
% 0.48/0.65  # ...remaining for further processing  : 579
% 0.48/0.65  # Other redundant clauses eliminated   : 5
% 0.48/0.65  # Clauses deleted for lack of memory   : 0
% 0.48/0.65  # Backward-subsumed                    : 39
% 0.48/0.65  # Backward-rewritten                   : 8
% 0.48/0.65  # Generated clauses                    : 16565
% 0.48/0.65  # ...of the previous two non-trivial   : 13477
% 0.48/0.65  # Contextual simplify-reflections      : 41
% 0.48/0.65  # Paramodulations                      : 16554
% 0.48/0.65  # Factorizations                       : 6
% 0.48/0.65  # Equation resolutions                 : 5
% 0.48/0.65  # Propositional unsat checks           : 0
% 0.48/0.65  #    Propositional check models        : 0
% 0.48/0.65  #    Propositional check unsatisfiable : 0
% 0.48/0.65  #    Propositional clauses             : 0
% 0.48/0.65  #    Propositional clauses after purity: 0
% 0.48/0.66  #    Propositional unsat core size     : 0
% 0.48/0.66  #    Propositional preprocessing time  : 0.000
% 0.48/0.66  #    Propositional encoding time       : 0.000
% 0.48/0.66  #    Propositional solver time         : 0.000
% 0.48/0.66  #    Success case prop preproc time    : 0.000
% 0.48/0.66  #    Success case prop encoding time   : 0.000
% 0.48/0.66  #    Success case prop solver time     : 0.000
% 0.48/0.66  # Current number of processed clauses  : 491
% 0.48/0.66  #    Positive orientable unit clauses  : 56
% 0.48/0.66  #    Positive unorientable unit clauses: 2
% 0.48/0.66  #    Negative unit clauses             : 7
% 0.48/0.66  #    Non-unit-clauses                  : 426
% 0.48/0.66  # Current number of unprocessed clauses: 10577
% 0.48/0.66  # ...number of literals in the above   : 39667
% 0.48/0.66  # Current number of archived formulas  : 0
% 0.48/0.66  # Current number of archived clauses   : 91
% 0.48/0.66  # Clause-clause subsumption calls (NU) : 41962
% 0.48/0.66  # Rec. Clause-clause subsumption calls : 26695
% 0.48/0.66  # Non-unit clause-clause subsumptions  : 1588
% 0.48/0.66  # Unit Clause-clause subsumption calls : 1061
% 0.48/0.66  # Rewrite failures with RHS unbound    : 0
% 0.48/0.66  # BW rewrite match attempts            : 110
% 0.48/0.66  # BW rewrite match successes           : 24
% 0.48/0.66  # Condensation attempts                : 0
% 0.48/0.66  # Condensation successes               : 0
% 0.48/0.66  # Termbank termtop insertions          : 263752
% 0.48/0.66  
% 0.48/0.66  # -------------------------------------------------
% 0.48/0.66  # User time                : 0.304 s
% 0.48/0.66  # System time              : 0.015 s
% 0.48/0.66  # Total time               : 0.319 s
% 0.48/0.66  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
