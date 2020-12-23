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
% DateTime   : Thu Dec  3 10:48:21 EST 2020

% Result     : Theorem 11.99s
% Output     : CNFRefutation 11.99s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 296 expanded)
%              Number of clauses        :   63 ( 142 expanded)
%              Number of leaves         :   19 (  74 expanded)
%              Depth                    :   20
%              Number of atoms          :  284 ( 785 expanded)
%              Number of equality atoms :   38 ( 164 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t7_tarski,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ! [X4] :
                  ~ ( r2_hidden(X4,X2)
                    & r2_hidden(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t31_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(c_0_19,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X16,X15)
        | r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | r2_hidden(X17,X15)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k2_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k2_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X20)
        | r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k2_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_20,plain,(
    ! [X45,X46] : k3_tarski(k2_tarski(X45,X46)) = k2_xboole_0(X45,X46) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k2_tarski(X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_25,plain,(
    ! [X27] : k2_xboole_0(X27,k1_xboole_0) = X27 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(k3_tarski(k2_tarski(X1,X2)),X3)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,plain,
    ( k3_tarski(k2_tarski(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_28,c_0_22])).

fof(c_0_31,plain,(
    ! [X47,X48,X50] :
      ( ( r2_hidden(esk3_2(X47,X48),X48)
        | ~ r2_hidden(X47,X48) )
      & ( ~ r2_hidden(X50,X48)
        | ~ r2_hidden(X50,esk3_2(X47,X48))
        | ~ r2_hidden(X47,X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).

fof(c_0_32,plain,(
    ! [X22,X23] :
      ( ( r1_tarski(X22,X23)
        | X22 != X23 )
      & ( r1_tarski(X23,X22)
        | X22 != X23 )
      & ( ~ r1_tarski(X22,X23)
        | ~ r1_tarski(X23,X22)
        | X22 = X23 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_33,plain,(
    ! [X31] : r1_tarski(k1_xboole_0,X31) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_36,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,esk3_2(X2,k1_xboole_0))
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( r1_tarski(esk3_2(X1,k1_xboole_0),X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,plain,
    ( esk3_2(X1,k1_xboole_0) = k1_xboole_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_44,plain,(
    ! [X57,X58,X59,X61,X62,X63,X64,X66] :
      ( ( ~ r2_hidden(X59,X58)
        | r2_hidden(k4_tarski(X59,esk4_3(X57,X58,X59)),X57)
        | X58 != k1_relat_1(X57) )
      & ( ~ r2_hidden(k4_tarski(X61,X62),X57)
        | r2_hidden(X61,X58)
        | X58 != k1_relat_1(X57) )
      & ( ~ r2_hidden(esk5_2(X63,X64),X64)
        | ~ r2_hidden(k4_tarski(esk5_2(X63,X64),X66),X63)
        | X64 = k1_relat_1(X63) )
      & ( r2_hidden(esk5_2(X63,X64),X64)
        | r2_hidden(k4_tarski(esk5_2(X63,X64),esk6_2(X63,X64)),X63)
        | X64 = k1_relat_1(X63) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_43]),c_0_34])).

cnf(c_0_46,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_47,plain,
    ( X1 != k1_relat_1(k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_48,plain,(
    ! [X24,X25,X26] :
      ( ~ r1_tarski(X24,X25)
      | r1_tarski(X24,k2_xboole_0(X26,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_47])).

fof(c_0_50,plain,(
    ! [X68] :
      ( ~ v1_relat_1(X68)
      | k3_relat_1(X68) = k2_xboole_0(k1_relat_1(X68),k2_relat_1(X68)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_51,plain,(
    ! [X28,X29,X30] :
      ( ~ r1_tarski(X28,X29)
      | ~ r1_tarski(X29,X30)
      | r1_tarski(X28,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_40])).

fof(c_0_54,plain,(
    ! [X55,X56] :
      ( ~ v1_relat_1(X55)
      | ~ m1_subset_1(X56,k1_zfmisc_1(X55))
      | v1_relat_1(X56) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_55,plain,(
    ! [X53,X54] :
      ( ( ~ m1_subset_1(X53,k1_zfmisc_1(X54))
        | r1_tarski(X53,X54) )
      & ( ~ r1_tarski(X53,X54)
        | m1_subset_1(X53,k1_zfmisc_1(X54)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_56,plain,(
    ! [X40,X41,X42] :
      ( ~ r1_tarski(X40,X41)
      | ~ r1_tarski(X42,X41)
      | r1_tarski(k2_xboole_0(X40,X42),X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_57,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_52,c_0_22])).

cnf(c_0_60,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_53])).

fof(c_0_61,plain,(
    ! [X34,X35,X36] :
      ( ~ r1_tarski(X34,k2_xboole_0(X35,X36))
      | r1_tarski(k4_xboole_0(X34,X35),X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_62,plain,(
    ! [X71,X72] :
      ( ( r1_tarski(k1_relat_1(X71),k1_relat_1(X72))
        | ~ r1_tarski(X71,X72)
        | ~ v1_relat_1(X72)
        | ~ v1_relat_1(X71) )
      & ( r1_tarski(k2_relat_1(X71),k2_relat_1(X72))
        | ~ r1_tarski(X71,X72)
        | ~ v1_relat_1(X72)
        | ~ v1_relat_1(X71) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_63,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,plain,
    ( k3_relat_1(X1) = k3_tarski(k2_tarski(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_57,c_0_22])).

fof(c_0_67,plain,(
    ! [X37,X38,X39] :
      ( ~ r1_tarski(k4_xboole_0(X37,X38),X39)
      | r1_tarski(X37,k2_xboole_0(X38,X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_69,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_47,c_0_60])).

cnf(c_0_70,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_72,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_73,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

fof(c_0_74,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_relat_1])).

cnf(c_0_75,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_65,c_0_22])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_66])).

cnf(c_0_77,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,k1_xboole_0)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_68,c_0_30])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,X2)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_40])).

cnf(c_0_81,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_70,c_0_22])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,k1_relat_1(X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])).

fof(c_0_83,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_relat_1(esk8_0)
    & r1_tarski(esk7_0,esk8_0)
    & ~ r1_tarski(k3_relat_1(esk7_0),k3_relat_1(esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_74])])])).

cnf(c_0_84,plain,
    ( r1_tarski(k3_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_66])).

cnf(c_0_85,plain,
    ( r1_tarski(k2_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_73])).

cnf(c_0_86,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_78,c_0_22])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,X2)
    | X3 != k1_xboole_0
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_88,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_81,c_0_30])).

cnf(c_0_89,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | r2_hidden(esk1_2(k1_relat_1(X1),X2),k1_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_82,c_0_40])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_91,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_92,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk7_0),k3_relat_1(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_93,plain,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_relat_1(X1),k3_relat_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_73])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k4_xboole_0(X1,k1_relat_1(X2)),k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_66])).

cnf(c_0_95,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_96,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk7_0),X1)
    | r2_hidden(esk1_2(k1_relat_1(esk7_0),X1),k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91])])).

cnf(c_0_98,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk7_0),k3_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_91]),c_0_90])])).

cnf(c_0_99,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk7_0),k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_91]),c_0_100])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:22:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 11.99/12.22  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 11.99/12.22  # and selection function PSelectComplexExceptUniqMaxHorn.
% 11.99/12.22  #
% 11.99/12.22  # Preprocessing time       : 0.030 s
% 11.99/12.22  
% 11.99/12.22  # Proof found!
% 11.99/12.22  # SZS status Theorem
% 11.99/12.22  # SZS output start CNFRefutation
% 11.99/12.22  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 11.99/12.22  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 11.99/12.22  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 11.99/12.22  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 11.99/12.22  fof(t7_tarski, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X2)&r2_hidden(X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 11.99/12.22  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.99/12.22  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.99/12.22  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.99/12.22  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 11.99/12.22  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 11.99/12.22  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 11.99/12.22  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 11.99/12.22  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.99/12.22  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.99/12.22  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 11.99/12.22  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 11.99/12.22  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 11.99/12.22  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 11.99/12.22  fof(t31_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 11.99/12.22  fof(c_0_19, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X16,X15)|(r2_hidden(X16,X13)|r2_hidden(X16,X14))|X15!=k2_xboole_0(X13,X14))&((~r2_hidden(X17,X13)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))&(~r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))))&(((~r2_hidden(esk2_3(X18,X19,X20),X18)|~r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|~r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19)))&(r2_hidden(esk2_3(X18,X19,X20),X20)|(r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k2_xboole_0(X18,X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 11.99/12.22  fof(c_0_20, plain, ![X45, X46]:k3_tarski(k2_tarski(X45,X46))=k2_xboole_0(X45,X46), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 11.99/12.22  cnf(c_0_21, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 11.99/12.22  cnf(c_0_22, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 11.99/12.22  fof(c_0_23, plain, ![X5, X6]:(~r2_hidden(X5,X6)|~r2_hidden(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 11.99/12.22  cnf(c_0_24, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k2_tarski(X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 11.99/12.22  fof(c_0_25, plain, ![X27]:k2_xboole_0(X27,k1_xboole_0)=X27, inference(variable_rename,[status(thm)],[t1_boole])).
% 11.99/12.22  cnf(c_0_26, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 11.99/12.22  cnf(c_0_27, plain, (r2_hidden(X1,k3_tarski(k2_tarski(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_24])).
% 11.99/12.22  cnf(c_0_28, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 11.99/12.22  cnf(c_0_29, plain, (~r2_hidden(k3_tarski(k2_tarski(X1,X2)),X3)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 11.99/12.22  cnf(c_0_30, plain, (k3_tarski(k2_tarski(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_28, c_0_22])).
% 11.99/12.22  fof(c_0_31, plain, ![X47, X48, X50]:((r2_hidden(esk3_2(X47,X48),X48)|~r2_hidden(X47,X48))&(~r2_hidden(X50,X48)|~r2_hidden(X50,esk3_2(X47,X48))|~r2_hidden(X47,X48))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).
% 11.99/12.22  fof(c_0_32, plain, ![X22, X23]:(((r1_tarski(X22,X23)|X22!=X23)&(r1_tarski(X23,X22)|X22!=X23))&(~r1_tarski(X22,X23)|~r1_tarski(X23,X22)|X22=X23)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 11.99/12.22  fof(c_0_33, plain, ![X31]:r1_tarski(k1_xboole_0,X31), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 11.99/12.22  cnf(c_0_34, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 11.99/12.22  cnf(c_0_35, plain, (r2_hidden(esk3_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 11.99/12.22  fof(c_0_36, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 11.99/12.22  cnf(c_0_37, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 11.99/12.22  cnf(c_0_38, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 11.99/12.22  cnf(c_0_39, plain, (~r2_hidden(X1,esk3_2(X2,k1_xboole_0))|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 11.99/12.22  cnf(c_0_40, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 11.99/12.22  cnf(c_0_41, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 11.99/12.22  cnf(c_0_42, plain, (r1_tarski(esk3_2(X1,k1_xboole_0),X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 11.99/12.22  cnf(c_0_43, plain, (esk3_2(X1,k1_xboole_0)=k1_xboole_0|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 11.99/12.22  fof(c_0_44, plain, ![X57, X58, X59, X61, X62, X63, X64, X66]:(((~r2_hidden(X59,X58)|r2_hidden(k4_tarski(X59,esk4_3(X57,X58,X59)),X57)|X58!=k1_relat_1(X57))&(~r2_hidden(k4_tarski(X61,X62),X57)|r2_hidden(X61,X58)|X58!=k1_relat_1(X57)))&((~r2_hidden(esk5_2(X63,X64),X64)|~r2_hidden(k4_tarski(esk5_2(X63,X64),X66),X63)|X64=k1_relat_1(X63))&(r2_hidden(esk5_2(X63,X64),X64)|r2_hidden(k4_tarski(esk5_2(X63,X64),esk6_2(X63,X64)),X63)|X64=k1_relat_1(X63)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 11.99/12.22  cnf(c_0_45, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_43]), c_0_34])).
% 11.99/12.22  cnf(c_0_46, plain, (r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 11.99/12.22  cnf(c_0_47, plain, (X1!=k1_relat_1(k1_xboole_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 11.99/12.22  fof(c_0_48, plain, ![X24, X25, X26]:(~r1_tarski(X24,X25)|r1_tarski(X24,k2_xboole_0(X26,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 11.99/12.22  cnf(c_0_49, plain, (~r2_hidden(X1,k1_relat_1(k1_xboole_0))), inference(er,[status(thm)],[c_0_47])).
% 11.99/12.22  fof(c_0_50, plain, ![X68]:(~v1_relat_1(X68)|k3_relat_1(X68)=k2_xboole_0(k1_relat_1(X68),k2_relat_1(X68))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 11.99/12.22  fof(c_0_51, plain, ![X28, X29, X30]:(~r1_tarski(X28,X29)|~r1_tarski(X29,X30)|r1_tarski(X28,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 11.99/12.22  cnf(c_0_52, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 11.99/12.22  cnf(c_0_53, plain, (r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_49, c_0_40])).
% 11.99/12.22  fof(c_0_54, plain, ![X55, X56]:(~v1_relat_1(X55)|(~m1_subset_1(X56,k1_zfmisc_1(X55))|v1_relat_1(X56))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 11.99/12.22  fof(c_0_55, plain, ![X53, X54]:((~m1_subset_1(X53,k1_zfmisc_1(X54))|r1_tarski(X53,X54))&(~r1_tarski(X53,X54)|m1_subset_1(X53,k1_zfmisc_1(X54)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 11.99/12.22  fof(c_0_56, plain, ![X40, X41, X42]:(~r1_tarski(X40,X41)|~r1_tarski(X42,X41)|r1_tarski(k2_xboole_0(X40,X42),X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 11.99/12.22  cnf(c_0_57, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 11.99/12.22  cnf(c_0_58, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 11.99/12.22  cnf(c_0_59, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_52, c_0_22])).
% 11.99/12.22  cnf(c_0_60, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_53])).
% 11.99/12.22  fof(c_0_61, plain, ![X34, X35, X36]:(~r1_tarski(X34,k2_xboole_0(X35,X36))|r1_tarski(k4_xboole_0(X34,X35),X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 11.99/12.22  fof(c_0_62, plain, ![X71, X72]:((r1_tarski(k1_relat_1(X71),k1_relat_1(X72))|~r1_tarski(X71,X72)|~v1_relat_1(X72)|~v1_relat_1(X71))&(r1_tarski(k2_relat_1(X71),k2_relat_1(X72))|~r1_tarski(X71,X72)|~v1_relat_1(X72)|~v1_relat_1(X71))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 11.99/12.22  cnf(c_0_63, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 11.99/12.22  cnf(c_0_64, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 11.99/12.22  cnf(c_0_65, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 11.99/12.22  cnf(c_0_66, plain, (k3_relat_1(X1)=k3_tarski(k2_tarski(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_57, c_0_22])).
% 11.99/12.22  fof(c_0_67, plain, ![X37, X38, X39]:(~r1_tarski(k4_xboole_0(X37,X38),X39)|r1_tarski(X37,k2_xboole_0(X38,X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 11.99/12.22  cnf(c_0_68, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X1,X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 11.99/12.22  cnf(c_0_69, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_47, c_0_60])).
% 11.99/12.22  cnf(c_0_70, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 11.99/12.22  cnf(c_0_71, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 11.99/12.22  cnf(c_0_72, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 11.99/12.22  cnf(c_0_73, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 11.99/12.22  fof(c_0_74, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t31_relat_1])).
% 11.99/12.22  cnf(c_0_75, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_65, c_0_22])).
% 11.99/12.22  cnf(c_0_76, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_59, c_0_66])).
% 11.99/12.22  cnf(c_0_77, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 11.99/12.22  cnf(c_0_78, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 11.99/12.22  cnf(c_0_79, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,k1_xboole_0)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_68, c_0_30])).
% 11.99/12.22  cnf(c_0_80, plain, (r1_tarski(X1,X2)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_69, c_0_40])).
% 11.99/12.22  cnf(c_0_81, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))), inference(rw,[status(thm)],[c_0_70, c_0_22])).
% 11.99/12.22  cnf(c_0_82, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X3,X2)|~r2_hidden(X1,k1_relat_1(X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])).
% 11.99/12.22  fof(c_0_83, negated_conjecture, (v1_relat_1(esk7_0)&(v1_relat_1(esk8_0)&(r1_tarski(esk7_0,esk8_0)&~r1_tarski(k3_relat_1(esk7_0),k3_relat_1(esk8_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_74])])])).
% 11.99/12.22  cnf(c_0_84, plain, (r1_tarski(k3_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_75, c_0_66])).
% 11.99/12.22  cnf(c_0_85, plain, (r1_tarski(k2_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_73])).
% 11.99/12.22  cnf(c_0_86, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_78, c_0_22])).
% 11.99/12.22  cnf(c_0_87, plain, (r1_tarski(X1,X2)|X3!=k1_xboole_0|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 11.99/12.22  cnf(c_0_88, plain, (r1_tarski(k4_xboole_0(X1,X2),k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_81, c_0_30])).
% 11.99/12.22  cnf(c_0_89, plain, (r1_tarski(k1_relat_1(X1),X2)|r2_hidden(esk1_2(k1_relat_1(X1),X2),k1_relat_1(X3))|~v1_relat_1(X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_82, c_0_40])).
% 11.99/12.22  cnf(c_0_90, negated_conjecture, (r1_tarski(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 11.99/12.22  cnf(c_0_91, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 11.99/12.22  cnf(c_0_92, negated_conjecture, (~r1_tarski(k3_relat_1(esk7_0),k3_relat_1(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 11.99/12.22  cnf(c_0_93, plain, (r1_tarski(k3_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(k1_relat_1(X1),k3_relat_1(X2))|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_73])).
% 11.99/12.22  cnf(c_0_94, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(k4_xboole_0(X1,k1_relat_1(X2)),k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_86, c_0_66])).
% 11.99/12.22  cnf(c_0_95, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 11.99/12.22  cnf(c_0_96, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 11.99/12.22  cnf(c_0_97, negated_conjecture, (r1_tarski(k1_relat_1(esk7_0),X1)|r2_hidden(esk1_2(k1_relat_1(esk7_0),X1),k1_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91])])).
% 11.99/12.22  cnf(c_0_98, negated_conjecture, (~r1_tarski(k1_relat_1(esk7_0),k3_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_91]), c_0_90])])).
% 11.99/12.22  cnf(c_0_99, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 11.99/12.22  cnf(c_0_100, negated_conjecture, (r1_tarski(k1_relat_1(esk7_0),k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 11.99/12.22  cnf(c_0_101, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_91]), c_0_100])]), ['proof']).
% 11.99/12.22  # SZS output end CNFRefutation
% 11.99/12.22  # Proof object total steps             : 102
% 11.99/12.22  # Proof object clause steps            : 63
% 11.99/12.22  # Proof object formula steps           : 39
% 11.99/12.22  # Proof object conjectures             : 10
% 11.99/12.22  # Proof object clause conjectures      : 7
% 11.99/12.22  # Proof object formula conjectures     : 3
% 11.99/12.22  # Proof object initial clauses used    : 24
% 11.99/12.22  # Proof object initial formulas used   : 19
% 11.99/12.22  # Proof object generating inferences   : 31
% 11.99/12.22  # Proof object simplifying inferences  : 20
% 11.99/12.22  # Training examples: 0 positive, 0 negative
% 11.99/12.22  # Parsed axioms                        : 23
% 11.99/12.22  # Removed by relevancy pruning/SinE    : 0
% 11.99/12.22  # Initial clauses                      : 41
% 11.99/12.22  # Removed in clause preprocessing      : 2
% 11.99/12.22  # Initial clauses in saturation        : 39
% 11.99/12.22  # Processed clauses                    : 11875
% 11.99/12.22  # ...of these trivial                  : 140
% 11.99/12.22  # ...subsumed                          : 8954
% 11.99/12.22  # ...remaining for further processing  : 2781
% 11.99/12.22  # Other redundant clauses eliminated   : 1423
% 11.99/12.22  # Clauses deleted for lack of memory   : 0
% 11.99/12.22  # Backward-subsumed                    : 198
% 11.99/12.22  # Backward-rewritten                   : 56
% 11.99/12.22  # Generated clauses                    : 466807
% 11.99/12.22  # ...of the previous two non-trivial   : 451146
% 11.99/12.22  # Contextual simplify-reflections      : 218
% 11.99/12.22  # Paramodulations                      : 461366
% 11.99/12.22  # Factorizations                       : 3820
% 11.99/12.22  # Equation resolutions                 : 1620
% 11.99/12.22  # Propositional unsat checks           : 0
% 11.99/12.22  #    Propositional check models        : 0
% 11.99/12.22  #    Propositional check unsatisfiable : 0
% 11.99/12.22  #    Propositional clauses             : 0
% 11.99/12.22  #    Propositional clauses after purity: 0
% 11.99/12.22  #    Propositional unsat core size     : 0
% 11.99/12.22  #    Propositional preprocessing time  : 0.000
% 11.99/12.22  #    Propositional encoding time       : 0.000
% 11.99/12.22  #    Propositional solver time         : 0.000
% 11.99/12.22  #    Success case prop preproc time    : 0.000
% 11.99/12.22  #    Success case prop encoding time   : 0.000
% 11.99/12.22  #    Success case prop solver time     : 0.000
% 11.99/12.22  # Current number of processed clauses  : 2524
% 11.99/12.22  #    Positive orientable unit clauses  : 86
% 11.99/12.22  #    Positive unorientable unit clauses: 1
% 11.99/12.22  #    Negative unit clauses             : 20
% 11.99/12.22  #    Non-unit-clauses                  : 2417
% 11.99/12.22  # Current number of unprocessed clauses: 438732
% 11.99/12.22  # ...number of literals in the above   : 2827286
% 11.99/12.22  # Current number of archived formulas  : 0
% 11.99/12.22  # Current number of archived clauses   : 257
% 11.99/12.22  # Clause-clause subsumption calls (NU) : 1480903
% 11.99/12.22  # Rec. Clause-clause subsumption calls : 355193
% 11.99/12.22  # Non-unit clause-clause subsumptions  : 5971
% 11.99/12.22  # Unit Clause-clause subsumption calls : 10082
% 11.99/12.22  # Rewrite failures with RHS unbound    : 0
% 11.99/12.22  # BW rewrite match attempts            : 1424
% 11.99/12.22  # BW rewrite match successes           : 12
% 11.99/12.22  # Condensation attempts                : 0
% 11.99/12.22  # Condensation successes               : 0
% 11.99/12.22  # Termbank termtop insertions          : 10985903
% 11.99/12.24  
% 11.99/12.24  # -------------------------------------------------
% 11.99/12.24  # User time                : 11.563 s
% 11.99/12.24  # System time              : 0.316 s
% 11.99/12.24  # Total time               : 11.879 s
% 11.99/12.24  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
