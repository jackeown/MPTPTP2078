%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:17 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  143 (2174 expanded)
%              Number of clauses        :   81 ( 807 expanded)
%              Number of leaves         :   31 ( 660 expanded)
%              Depth                    :   15
%              Number of atoms          :  316 (3527 expanded)
%              Number of equality atoms :  110 (2118 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t61_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k1_tarski(X1),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => r2_hidden(k1_funct_1(X3,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))
     => ( k1_mcart_1(X1) = X2
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(l33_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t6_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6,X7] :
                  ( ( r2_hidden(X3,X4)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X6,X7)
                    & r2_hidden(X7,X2) )
                 => r1_xboole_0(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

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

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t12_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t91_mcart_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => ( r2_hidden(k1_mcart_1(X2),k1_relat_1(X1))
            & r2_hidden(k2_mcart_1(X2),k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_mcart_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t2_zfmisc_1,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r2_hidden(k1_funct_1(X3,X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t61_funct_2])).

fof(c_0_32,plain,(
    ! [X58,X59] : k1_setfam_1(k2_tarski(X58,X59)) = k3_xboole_0(X58,X59) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_33,plain,(
    ! [X23,X24] : k1_enumset1(X23,X23,X24) = k2_tarski(X23,X24) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_34,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0)))
    & esk4_0 != k1_xboole_0
    & ~ r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

fof(c_0_35,plain,(
    ! [X22] : k2_tarski(X22,X22) = k1_tarski(X22) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_36,plain,(
    ! [X25,X26,X27] : k2_enumset1(X25,X25,X26,X27) = k1_enumset1(X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_37,plain,(
    ! [X28,X29,X30,X31] : k3_enumset1(X28,X28,X29,X30,X31) = k2_enumset1(X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_38,plain,(
    ! [X32,X33,X34,X35,X36] : k4_enumset1(X32,X32,X33,X34,X35,X36) = k3_enumset1(X32,X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_39,plain,(
    ! [X37,X38,X39,X40,X41,X42] : k5_enumset1(X37,X37,X38,X39,X40,X41,X42) = k4_enumset1(X37,X38,X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_40,plain,(
    ! [X43,X44,X45,X46,X47,X48,X49] : k6_enumset1(X43,X43,X44,X45,X46,X47,X48,X49) = k5_enumset1(X43,X44,X45,X46,X47,X48,X49) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_41,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_42,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_44,plain,(
    ! [X78,X79,X80] :
      ( ( k1_mcart_1(X78) = X79
        | ~ r2_hidden(X78,k2_zfmisc_1(k1_tarski(X79),X80)) )
      & ( r2_hidden(k2_mcart_1(X78),X80)
        | ~ r2_hidden(X78,k2_zfmisc_1(k1_tarski(X79),X80)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_mcart_1])])])).

fof(c_0_45,plain,(
    ! [X75,X76,X77] :
      ( ~ m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X75,X76)))
      | k1_relset_1(X75,X76,X77) = k1_relat_1(X77) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_53,plain,(
    ! [X50,X51] :
      ( ( k4_xboole_0(k1_tarski(X50),X51) != k1_tarski(X50)
        | ~ r2_hidden(X50,X51) )
      & ( r2_hidden(X50,X51)
        | k4_xboole_0(k1_tarski(X50),X51) = k1_tarski(X50) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_55,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_56,plain,(
    ! [X18] : k3_xboole_0(X18,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_57,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk1_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk1_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_58,plain,(
    ! [X65,X66] :
      ( ( ~ v5_relat_1(X66,X65)
        | r1_tarski(k2_relat_1(X66),X65)
        | ~ v1_relat_1(X66) )
      & ( ~ r1_tarski(k2_relat_1(X66),X65)
        | v5_relat_1(X66,X65)
        | ~ v1_relat_1(X66) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_59,plain,(
    ! [X54,X55,X56] :
      ( ~ m1_subset_1(X55,k1_zfmisc_1(X54))
      | ~ r2_hidden(X56,X55)
      | r2_hidden(X56,X54) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_60,plain,(
    ! [X57] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X57)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_61,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(k1_tarski(X3),X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_62,plain,(
    ! [X81,X83,X84,X85,X86,X87] :
      ( ( r2_hidden(esk2_1(X81),X81)
        | X81 = k1_xboole_0 )
      & ( ~ r2_hidden(X83,X84)
        | ~ r2_hidden(X84,X85)
        | ~ r2_hidden(X85,X86)
        | ~ r2_hidden(X86,X87)
        | ~ r2_hidden(X87,esk2_1(X81))
        | r1_xboole_0(X83,X81)
        | X81 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).

fof(c_0_63,plain,(
    ! [X90,X91,X92] :
      ( ( ~ v1_funct_2(X92,X90,X91)
        | X90 = k1_relset_1(X90,X91,X92)
        | X91 = k1_xboole_0
        | ~ m1_subset_1(X92,k1_zfmisc_1(k2_zfmisc_1(X90,X91))) )
      & ( X90 != k1_relset_1(X90,X91,X92)
        | v1_funct_2(X92,X90,X91)
        | X91 = k1_xboole_0
        | ~ m1_subset_1(X92,k1_zfmisc_1(k2_zfmisc_1(X90,X91))) )
      & ( ~ v1_funct_2(X92,X90,X91)
        | X90 = k1_relset_1(X90,X91,X92)
        | X90 != k1_xboole_0
        | ~ m1_subset_1(X92,k1_zfmisc_1(k2_zfmisc_1(X90,X91))) )
      & ( X90 != k1_relset_1(X90,X91,X92)
        | v1_funct_2(X92,X90,X91)
        | X90 != k1_xboole_0
        | ~ m1_subset_1(X92,k1_zfmisc_1(k2_zfmisc_1(X90,X91))) )
      & ( ~ v1_funct_2(X92,X90,X91)
        | X92 = k1_xboole_0
        | X90 = k1_xboole_0
        | X91 != k1_xboole_0
        | ~ m1_subset_1(X92,k1_zfmisc_1(k2_zfmisc_1(X90,X91))) )
      & ( X92 != k1_xboole_0
        | v1_funct_2(X92,X90,X91)
        | X90 = k1_xboole_0
        | X91 != k1_xboole_0
        | ~ m1_subset_1(X92,k1_zfmisc_1(k2_zfmisc_1(X90,X91))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_65,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_43]),c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_67,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) != k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_70,plain,(
    ! [X19] : k5_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_71,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_72,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_73,plain,(
    ! [X67,X68] :
      ( ~ v1_relat_1(X68)
      | ~ v1_funct_1(X68)
      | ~ r2_hidden(X67,k1_relat_1(X68))
      | r2_hidden(k1_funct_1(X68,X67),k2_relat_1(X68)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

cnf(c_0_74,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_75,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_76,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_47]),c_0_43]),c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_77,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_78,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_2(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_47]),c_0_43]),c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_80,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_81,negated_conjecture,
    ( k1_relset_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_82,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_47]),c_0_47]),c_0_43]),c_0_43]),c_0_68]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52]),c_0_52])).

cnf(c_0_83,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_55]),c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_84,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,X2)
    | ~ v5_relat_1(X3,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k2_relat_1(X3)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_86,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_88,plain,
    ( k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) = k1_xboole_0
    | r2_hidden(k2_mcart_1(esk2_1(k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))),X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_89,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_90,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k1_relat_1(esk5_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_66]),c_0_79])]),c_0_80]),c_0_81])).

cnf(c_0_91,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])])).

cnf(c_0_92,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ v5_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

fof(c_0_93,plain,(
    ! [X69,X70,X71] :
      ( ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))
      | v1_relat_1(X71) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_94,plain,
    ( k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_xboole_0) = k1_xboole_0
    | r2_hidden(k2_mcart_1(esk2_1(k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_xboole_0))),X2) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_95,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_47]),c_0_43]),c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0))) ),
    inference(rw,[status(thm)],[c_0_66,c_0_90])).

fof(c_0_97,plain,(
    ! [X52] : k3_tarski(k1_tarski(X52)) = X52 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

cnf(c_0_98,plain,
    ( ~ v1_funct_1(X1)
    | ~ v5_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_99,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

fof(c_0_100,plain,(
    ! [X72,X73,X74] :
      ( ( v4_relat_1(X74,X72)
        | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X72,X73))) )
      & ( v5_relat_1(X74,X73)
        | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X72,X73))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_101,negated_conjecture,
    ( k2_zfmisc_1(k1_relat_1(esk5_0),k1_xboole_0) = k1_xboole_0
    | r2_hidden(k2_mcart_1(esk2_1(k2_zfmisc_1(k1_relat_1(esk5_0),k1_xboole_0))),X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_90])).

fof(c_0_102,plain,(
    ! [X88,X89] :
      ( ( r2_hidden(k1_mcart_1(X89),k1_relat_1(X88))
        | ~ r2_hidden(X89,X88)
        | ~ v1_relat_1(X88) )
      & ( r2_hidden(k2_mcart_1(X89),k2_relat_1(X88))
        | ~ r2_hidden(X89,X88)
        | ~ v1_relat_1(X88) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_mcart_1])])])])).

cnf(c_0_103,negated_conjecture,
    ( k1_mcart_1(X1) = esk3_0
    | ~ r2_hidden(X1,k2_zfmisc_1(k1_relat_1(esk5_0),X2)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_90])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_96])).

fof(c_0_105,plain,(
    ! [X20,X21] : k2_tarski(X20,X21) = k2_tarski(X21,X20) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_106,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_107,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v5_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_77])).

cnf(c_0_108,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_109,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_66])).

cnf(c_0_110,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_111,negated_conjecture,
    ( k2_zfmisc_1(k1_relat_1(esk5_0),k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_101])).

cnf(c_0_112,plain,
    ( r2_hidden(k1_mcart_1(X1),k1_relat_1(X2))
    | ~ r2_hidden(X1,X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_113,negated_conjecture,
    ( k1_mcart_1(X1) = esk3_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_114,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

fof(c_0_115,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_116,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_47]),c_0_43]),c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_117,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | ~ v5_relat_1(esk5_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109])])).

cnf(c_0_118,negated_conjecture,
    ( v5_relat_1(X1,k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_119,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,esk5_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_120,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_121,negated_conjecture,
    ( v5_relat_1(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_66])).

cnf(c_0_122,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_43]),c_0_43]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52])).

cnf(c_0_123,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_115])).

cnf(c_0_124,negated_conjecture,
    ( k3_tarski(k1_relat_1(esk5_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_116,c_0_90])).

cnf(c_0_125,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_126,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).

cnf(c_0_127,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk3_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk2_1(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_119,c_0_77])).

cnf(c_0_128,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_92]),c_0_108]),c_0_121]),c_0_109])])).

fof(c_0_129,plain,(
    ! [X60,X61] :
      ( ~ m1_subset_1(X60,X61)
      | v1_xboole_0(X61)
      | r2_hidden(X60,X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_130,plain,(
    ! [X53] : ~ v1_xboole_0(k1_zfmisc_1(X53)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_131,negated_conjecture,
    ( k5_xboole_0(k1_relat_1(esk5_0),k1_setfam_1(k6_enumset1(k1_relat_1(esk5_0),k1_relat_1(esk5_0),k1_relat_1(esk5_0),k1_relat_1(esk5_0),k1_relat_1(esk5_0),k1_relat_1(esk5_0),k1_relat_1(esk5_0),X1))) != k1_relat_1(esk5_0)
    | ~ r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_90])).

cnf(c_0_132,plain,
    ( k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_83,c_0_122])).

cnf(c_0_133,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_84,c_0_123])).

cnf(c_0_134,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_126])).

cnf(c_0_135,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_77]),c_0_109])]),c_0_128])).

cnf(c_0_136,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_129])).

cnf(c_0_137,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_130])).

cnf(c_0_138,negated_conjecture,
    ( ~ m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_125]),c_0_132]),c_0_133])])).

cnf(c_0_139,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_134,c_0_135]),c_0_75])])).

cnf(c_0_140,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_75]),c_0_137])).

cnf(c_0_141,negated_conjecture,
    ( ~ r2_hidden(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_138,c_0_135]),c_0_75])]),c_0_139])).

cnf(c_0_142,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_140,c_0_141]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:47 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.52  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_URBAN_S0Y
% 0.19/0.52  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.52  #
% 0.19/0.52  # Preprocessing time       : 0.056 s
% 0.19/0.52  
% 0.19/0.52  # Proof found!
% 0.19/0.52  # SZS status Theorem
% 0.19/0.52  # SZS output start CNFRefutation
% 0.19/0.52  fof(t61_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 0.19/0.52  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.52  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.52  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.52  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.52  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.52  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.52  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.52  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.52  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.52  fof(t12_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))=>(k1_mcart_1(X1)=X2&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 0.19/0.52  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.52  fof(l33_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 0.19/0.52  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.19/0.52  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.52  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.19/0.52  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.52  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.52  fof(t6_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6, X7]:(((((r2_hidden(X3,X4)&r2_hidden(X4,X5))&r2_hidden(X5,X6))&r2_hidden(X6,X7))&r2_hidden(X7,X2))=>r1_xboole_0(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 0.19/0.52  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.52  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.52  fof(t12_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 0.19/0.52  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.52  fof(t31_zfmisc_1, axiom, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 0.19/0.52  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.52  fof(t91_mcart_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r2_hidden(X2,X1)=>(r2_hidden(k1_mcart_1(X2),k1_relat_1(X1))&r2_hidden(k2_mcart_1(X2),k2_relat_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_mcart_1)).
% 0.19/0.52  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.52  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.19/0.52  fof(t2_zfmisc_1, axiom, k3_tarski(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 0.19/0.52  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.52  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.19/0.52  fof(c_0_31, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2)))), inference(assume_negation,[status(cth)],[t61_funct_2])).
% 0.19/0.52  fof(c_0_32, plain, ![X58, X59]:k1_setfam_1(k2_tarski(X58,X59))=k3_xboole_0(X58,X59), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.52  fof(c_0_33, plain, ![X23, X24]:k1_enumset1(X23,X23,X24)=k2_tarski(X23,X24), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.52  fof(c_0_34, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))))&(esk4_0!=k1_xboole_0&~r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.19/0.52  fof(c_0_35, plain, ![X22]:k2_tarski(X22,X22)=k1_tarski(X22), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.52  fof(c_0_36, plain, ![X25, X26, X27]:k2_enumset1(X25,X25,X26,X27)=k1_enumset1(X25,X26,X27), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.52  fof(c_0_37, plain, ![X28, X29, X30, X31]:k3_enumset1(X28,X28,X29,X30,X31)=k2_enumset1(X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.52  fof(c_0_38, plain, ![X32, X33, X34, X35, X36]:k4_enumset1(X32,X32,X33,X34,X35,X36)=k3_enumset1(X32,X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.52  fof(c_0_39, plain, ![X37, X38, X39, X40, X41, X42]:k5_enumset1(X37,X37,X38,X39,X40,X41,X42)=k4_enumset1(X37,X38,X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.52  fof(c_0_40, plain, ![X43, X44, X45, X46, X47, X48, X49]:k6_enumset1(X43,X43,X44,X45,X46,X47,X48,X49)=k5_enumset1(X43,X44,X45,X46,X47,X48,X49), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.52  fof(c_0_41, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.52  cnf(c_0_42, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.52  cnf(c_0_43, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.52  fof(c_0_44, plain, ![X78, X79, X80]:((k1_mcart_1(X78)=X79|~r2_hidden(X78,k2_zfmisc_1(k1_tarski(X79),X80)))&(r2_hidden(k2_mcart_1(X78),X80)|~r2_hidden(X78,k2_zfmisc_1(k1_tarski(X79),X80)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_mcart_1])])])).
% 0.19/0.52  fof(c_0_45, plain, ![X75, X76, X77]:(~m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X75,X76)))|k1_relset_1(X75,X76,X77)=k1_relat_1(X77)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.52  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.52  cnf(c_0_47, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.52  cnf(c_0_48, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.52  cnf(c_0_49, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.52  cnf(c_0_50, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.52  cnf(c_0_51, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.52  cnf(c_0_52, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.52  fof(c_0_53, plain, ![X50, X51]:((k4_xboole_0(k1_tarski(X50),X51)!=k1_tarski(X50)|~r2_hidden(X50,X51))&(r2_hidden(X50,X51)|k4_xboole_0(k1_tarski(X50),X51)=k1_tarski(X50))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).
% 0.19/0.52  cnf(c_0_54, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.52  cnf(c_0_55, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.52  fof(c_0_56, plain, ![X18]:k3_xboole_0(X18,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.19/0.52  fof(c_0_57, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk1_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk1_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.52  fof(c_0_58, plain, ![X65, X66]:((~v5_relat_1(X66,X65)|r1_tarski(k2_relat_1(X66),X65)|~v1_relat_1(X66))&(~r1_tarski(k2_relat_1(X66),X65)|v5_relat_1(X66,X65)|~v1_relat_1(X66))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.19/0.52  fof(c_0_59, plain, ![X54, X55, X56]:(~m1_subset_1(X55,k1_zfmisc_1(X54))|(~r2_hidden(X56,X55)|r2_hidden(X56,X54))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.52  fof(c_0_60, plain, ![X57]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X57)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.52  cnf(c_0_61, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(k1_tarski(X3),X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.52  fof(c_0_62, plain, ![X81, X83, X84, X85, X86, X87]:((r2_hidden(esk2_1(X81),X81)|X81=k1_xboole_0)&(~r2_hidden(X83,X84)|~r2_hidden(X84,X85)|~r2_hidden(X85,X86)|~r2_hidden(X86,X87)|~r2_hidden(X87,esk2_1(X81))|r1_xboole_0(X83,X81)|X81=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_mcart_1])])])])])])).
% 0.19/0.52  fof(c_0_63, plain, ![X90, X91, X92]:((((~v1_funct_2(X92,X90,X91)|X90=k1_relset_1(X90,X91,X92)|X91=k1_xboole_0|~m1_subset_1(X92,k1_zfmisc_1(k2_zfmisc_1(X90,X91))))&(X90!=k1_relset_1(X90,X91,X92)|v1_funct_2(X92,X90,X91)|X91=k1_xboole_0|~m1_subset_1(X92,k1_zfmisc_1(k2_zfmisc_1(X90,X91)))))&((~v1_funct_2(X92,X90,X91)|X90=k1_relset_1(X90,X91,X92)|X90!=k1_xboole_0|~m1_subset_1(X92,k1_zfmisc_1(k2_zfmisc_1(X90,X91))))&(X90!=k1_relset_1(X90,X91,X92)|v1_funct_2(X92,X90,X91)|X90!=k1_xboole_0|~m1_subset_1(X92,k1_zfmisc_1(k2_zfmisc_1(X90,X91))))))&((~v1_funct_2(X92,X90,X91)|X92=k1_xboole_0|X90=k1_xboole_0|X91!=k1_xboole_0|~m1_subset_1(X92,k1_zfmisc_1(k2_zfmisc_1(X90,X91))))&(X92!=k1_xboole_0|v1_funct_2(X92,X90,X91)|X90=k1_xboole_0|X91!=k1_xboole_0|~m1_subset_1(X92,k1_zfmisc_1(k2_zfmisc_1(X90,X91)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.52  cnf(c_0_64, negated_conjecture, (v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.52  cnf(c_0_65, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.52  cnf(c_0_66, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_43]), c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_52])).
% 0.19/0.52  cnf(c_0_67, plain, (k4_xboole_0(k1_tarski(X1),X2)!=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.52  cnf(c_0_68, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.52  cnf(c_0_69, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.52  fof(c_0_70, plain, ![X19]:k5_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.52  cnf(c_0_71, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.52  cnf(c_0_72, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.52  fof(c_0_73, plain, ![X67, X68]:(~v1_relat_1(X68)|~v1_funct_1(X68)|(~r2_hidden(X67,k1_relat_1(X68))|r2_hidden(k1_funct_1(X68,X67),k2_relat_1(X68)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).
% 0.19/0.52  cnf(c_0_74, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.52  cnf(c_0_75, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.52  cnf(c_0_76, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_47]), c_0_43]), c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_52])).
% 0.19/0.52  cnf(c_0_77, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.52  cnf(c_0_78, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.52  cnf(c_0_79, negated_conjecture, (v1_funct_2(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_47]), c_0_43]), c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_52])).
% 0.19/0.52  cnf(c_0_80, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.52  cnf(c_0_81, negated_conjecture, (k1_relset_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0,esk5_0)=k1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.52  cnf(c_0_82, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)))!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_47]), c_0_47]), c_0_43]), c_0_43]), c_0_68]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52]), c_0_52])).
% 0.19/0.52  cnf(c_0_83, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_55]), c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_52])).
% 0.19/0.52  cnf(c_0_84, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.19/0.52  cnf(c_0_85, plain, (r2_hidden(X1,X2)|~v5_relat_1(X3,X2)|~v1_relat_1(X3)|~r2_hidden(X1,k2_relat_1(X3))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.19/0.52  cnf(c_0_86, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.52  cnf(c_0_87, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.19/0.52  cnf(c_0_88, plain, (k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)=k1_xboole_0|r2_hidden(k2_mcart_1(esk2_1(k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))),X2)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.19/0.52  cnf(c_0_89, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.52  cnf(c_0_90, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k1_relat_1(esk5_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_66]), c_0_79])]), c_0_80]), c_0_81])).
% 0.19/0.52  cnf(c_0_91, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])])).
% 0.19/0.52  cnf(c_0_92, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~v1_funct_1(X1)|~v5_relat_1(X1,X3)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.19/0.52  fof(c_0_93, plain, ![X69, X70, X71]:(~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))|v1_relat_1(X71)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.52  cnf(c_0_94, plain, (k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_xboole_0)=k1_xboole_0|r2_hidden(k2_mcart_1(esk2_1(k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_xboole_0))),X2)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.19/0.52  cnf(c_0_95, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_47]), c_0_43]), c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_52])).
% 0.19/0.52  cnf(c_0_96, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0)))), inference(rw,[status(thm)],[c_0_66, c_0_90])).
% 0.19/0.52  fof(c_0_97, plain, ![X52]:k3_tarski(k1_tarski(X52))=X52, inference(variable_rename,[status(thm)],[t31_zfmisc_1])).
% 0.19/0.52  cnf(c_0_98, plain, (~v1_funct_1(X1)|~v5_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.19/0.52  cnf(c_0_99, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.19/0.52  fof(c_0_100, plain, ![X72, X73, X74]:((v4_relat_1(X74,X72)|~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X72,X73))))&(v5_relat_1(X74,X73)|~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X72,X73))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.52  cnf(c_0_101, negated_conjecture, (k2_zfmisc_1(k1_relat_1(esk5_0),k1_xboole_0)=k1_xboole_0|r2_hidden(k2_mcart_1(esk2_1(k2_zfmisc_1(k1_relat_1(esk5_0),k1_xboole_0))),X1)), inference(spm,[status(thm)],[c_0_94, c_0_90])).
% 0.19/0.52  fof(c_0_102, plain, ![X88, X89]:((r2_hidden(k1_mcart_1(X89),k1_relat_1(X88))|~r2_hidden(X89,X88)|~v1_relat_1(X88))&(r2_hidden(k2_mcart_1(X89),k2_relat_1(X88))|~r2_hidden(X89,X88)|~v1_relat_1(X88))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_mcart_1])])])])).
% 0.19/0.52  cnf(c_0_103, negated_conjecture, (k1_mcart_1(X1)=esk3_0|~r2_hidden(X1,k2_zfmisc_1(k1_relat_1(esk5_0),X2))), inference(spm,[status(thm)],[c_0_95, c_0_90])).
% 0.19/0.52  cnf(c_0_104, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_74, c_0_96])).
% 0.19/0.52  fof(c_0_105, plain, ![X20, X21]:k2_tarski(X20,X21)=k2_tarski(X21,X20), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.52  cnf(c_0_106, plain, (k3_tarski(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.19/0.52  cnf(c_0_107, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_funct_1(X1)|~v5_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_98, c_0_77])).
% 0.19/0.52  cnf(c_0_108, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.52  cnf(c_0_109, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_99, c_0_66])).
% 0.19/0.52  cnf(c_0_110, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.19/0.52  cnf(c_0_111, negated_conjecture, (k2_zfmisc_1(k1_relat_1(esk5_0),k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_91, c_0_101])).
% 0.19/0.52  cnf(c_0_112, plain, (r2_hidden(k1_mcart_1(X1),k1_relat_1(X2))|~r2_hidden(X1,X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.19/0.52  cnf(c_0_113, negated_conjecture, (k1_mcart_1(X1)=esk3_0|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.19/0.52  cnf(c_0_114, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_105])).
% 0.19/0.52  fof(c_0_115, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k5_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.19/0.52  cnf(c_0_116, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_47]), c_0_43]), c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_52])).
% 0.19/0.52  cnf(c_0_117, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|~v5_relat_1(esk5_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_109])])).
% 0.19/0.52  cnf(c_0_118, negated_conjecture, (v5_relat_1(X1,k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_110, c_0_111])).
% 0.19/0.52  cnf(c_0_119, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(X1))|~v1_relat_1(X1)|~r2_hidden(X2,esk5_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 0.19/0.52  cnf(c_0_120, negated_conjecture, (~r2_hidden(k1_funct_1(esk5_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.52  cnf(c_0_121, negated_conjecture, (v5_relat_1(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_110, c_0_66])).
% 0.19/0.52  cnf(c_0_122, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_43]), c_0_43]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_52]), c_0_52])).
% 0.19/0.52  cnf(c_0_123, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_115])).
% 0.19/0.52  cnf(c_0_124, negated_conjecture, (k3_tarski(k1_relat_1(esk5_0))=esk3_0), inference(spm,[status(thm)],[c_0_116, c_0_90])).
% 0.19/0.52  cnf(c_0_125, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|~m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_117, c_0_118])).
% 0.19/0.52  cnf(c_0_126, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).
% 0.19/0.52  cnf(c_0_127, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk3_0,k1_relat_1(X1))|~v1_relat_1(X1)|~r2_hidden(esk2_1(esk5_0),X1)), inference(spm,[status(thm)],[c_0_119, c_0_77])).
% 0.19/0.52  cnf(c_0_128, negated_conjecture, (~r2_hidden(esk3_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_92]), c_0_108]), c_0_121]), c_0_109])])).
% 0.19/0.52  fof(c_0_129, plain, ![X60, X61]:(~m1_subset_1(X60,X61)|(v1_xboole_0(X61)|r2_hidden(X60,X61))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.52  fof(c_0_130, plain, ![X53]:~v1_xboole_0(k1_zfmisc_1(X53)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.19/0.52  cnf(c_0_131, negated_conjecture, (k5_xboole_0(k1_relat_1(esk5_0),k1_setfam_1(k6_enumset1(k1_relat_1(esk5_0),k1_relat_1(esk5_0),k1_relat_1(esk5_0),k1_relat_1(esk5_0),k1_relat_1(esk5_0),k1_relat_1(esk5_0),k1_relat_1(esk5_0),X1)))!=k1_relat_1(esk5_0)|~r2_hidden(esk3_0,X1)), inference(spm,[status(thm)],[c_0_82, c_0_90])).
% 0.19/0.52  cnf(c_0_132, plain, (k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_83, c_0_122])).
% 0.19/0.52  cnf(c_0_133, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_84, c_0_123])).
% 0.19/0.52  cnf(c_0_134, negated_conjecture, (esk3_0=k1_xboole_0|~m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_126])).
% 0.19/0.52  cnf(c_0_135, negated_conjecture, (esk5_0=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_77]), c_0_109])]), c_0_128])).
% 0.19/0.52  cnf(c_0_136, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_129])).
% 0.19/0.52  cnf(c_0_137, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_130])).
% 0.19/0.52  cnf(c_0_138, negated_conjecture, (~m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))|~r2_hidden(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_125]), c_0_132]), c_0_133])])).
% 0.19/0.52  cnf(c_0_139, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_134, c_0_135]), c_0_75])])).
% 0.19/0.52  cnf(c_0_140, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_75]), c_0_137])).
% 0.19/0.52  cnf(c_0_141, negated_conjecture, (~r2_hidden(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_138, c_0_135]), c_0_75])]), c_0_139])).
% 0.19/0.52  cnf(c_0_142, plain, ($false), inference(sr,[status(thm)],[c_0_140, c_0_141]), ['proof']).
% 0.19/0.52  # SZS output end CNFRefutation
% 0.19/0.52  # Proof object total steps             : 143
% 0.19/0.52  # Proof object clause steps            : 81
% 0.19/0.52  # Proof object formula steps           : 62
% 0.19/0.52  # Proof object conjectures             : 33
% 0.19/0.52  # Proof object clause conjectures      : 30
% 0.19/0.52  # Proof object formula conjectures     : 3
% 0.19/0.52  # Proof object initial clauses used    : 36
% 0.19/0.52  # Proof object initial formulas used   : 31
% 0.19/0.52  # Proof object generating inferences   : 31
% 0.19/0.52  # Proof object simplifying inferences  : 124
% 0.19/0.52  # Training examples: 0 positive, 0 negative
% 0.19/0.52  # Parsed axioms                        : 33
% 0.19/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.52  # Initial clauses                      : 51
% 0.19/0.52  # Removed in clause preprocessing      : 9
% 0.19/0.52  # Initial clauses in saturation        : 42
% 0.19/0.52  # Processed clauses                    : 712
% 0.19/0.52  # ...of these trivial                  : 12
% 0.19/0.52  # ...subsumed                          : 366
% 0.19/0.52  # ...remaining for further processing  : 334
% 0.19/0.52  # Other redundant clauses eliminated   : 6
% 0.19/0.52  # Clauses deleted for lack of memory   : 0
% 0.19/0.52  # Backward-subsumed                    : 13
% 0.19/0.52  # Backward-rewritten                   : 82
% 0.19/0.52  # Generated clauses                    : 3394
% 0.19/0.52  # ...of the previous two non-trivial   : 3225
% 0.19/0.52  # Contextual simplify-reflections      : 9
% 0.19/0.52  # Paramodulations                      : 3381
% 0.19/0.52  # Factorizations                       : 6
% 0.19/0.52  # Equation resolutions                 : 6
% 0.19/0.52  # Propositional unsat checks           : 0
% 0.19/0.52  #    Propositional check models        : 0
% 0.19/0.52  #    Propositional check unsatisfiable : 0
% 0.19/0.52  #    Propositional clauses             : 0
% 0.19/0.52  #    Propositional clauses after purity: 0
% 0.19/0.52  #    Propositional unsat core size     : 0
% 0.19/0.52  #    Propositional preprocessing time  : 0.000
% 0.19/0.52  #    Propositional encoding time       : 0.000
% 0.19/0.52  #    Propositional solver time         : 0.000
% 0.19/0.52  #    Success case prop preproc time    : 0.000
% 0.19/0.52  #    Success case prop encoding time   : 0.000
% 0.19/0.52  #    Success case prop solver time     : 0.000
% 0.19/0.52  # Current number of processed clauses  : 238
% 0.19/0.52  #    Positive orientable unit clauses  : 18
% 0.19/0.52  #    Positive unorientable unit clauses: 2
% 0.19/0.52  #    Negative unit clauses             : 5
% 0.19/0.52  #    Non-unit-clauses                  : 213
% 0.19/0.52  # Current number of unprocessed clauses: 1912
% 0.19/0.52  # ...number of literals in the above   : 14052
% 0.19/0.52  # Current number of archived formulas  : 0
% 0.19/0.52  # Current number of archived clauses   : 105
% 0.19/0.52  # Clause-clause subsumption calls (NU) : 19607
% 0.19/0.52  # Rec. Clause-clause subsumption calls : 3242
% 0.19/0.52  # Non-unit clause-clause subsumptions  : 310
% 0.19/0.52  # Unit Clause-clause subsumption calls : 166
% 0.19/0.52  # Rewrite failures with RHS unbound    : 0
% 0.19/0.52  # BW rewrite match attempts            : 19
% 0.19/0.52  # BW rewrite match successes           : 12
% 0.19/0.52  # Condensation attempts                : 0
% 0.19/0.52  # Condensation successes               : 0
% 0.19/0.52  # Termbank termtop insertions          : 79502
% 0.19/0.52  
% 0.19/0.52  # -------------------------------------------------
% 0.19/0.52  # User time                : 0.178 s
% 0.19/0.52  # System time              : 0.009 s
% 0.19/0.52  # Total time               : 0.187 s
% 0.19/0.52  # Maximum resident set size: 1616 pages
%------------------------------------------------------------------------------
