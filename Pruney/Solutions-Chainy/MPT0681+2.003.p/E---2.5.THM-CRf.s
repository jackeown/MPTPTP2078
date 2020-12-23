%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:27 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 427 expanded)
%              Number of clauses        :   46 ( 195 expanded)
%              Number of leaves         :   15 ( 112 expanded)
%              Depth                    :   14
%              Number of atoms          :  182 ( 948 expanded)
%              Number of equality atoms :   40 ( 156 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t207_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_xboole_0(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X1),X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(t110_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(t125_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_xboole_0(X1,X2)
          & v2_funct_1(X3) )
       => r1_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_funct_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( r2_hidden(X1,k2_relat_1(X2))
          & ! [X3] : ~ r2_hidden(X3,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

fof(t56_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),X1)
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

fof(t121_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( v2_funct_1(X3)
       => k9_relat_1(X3,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(t75_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_xboole_0(k3_xboole_0(X1,X2),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(c_0_15,plain,(
    ! [X5,X6] :
      ( ~ r1_xboole_0(X5,X6)
      | r1_xboole_0(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_16,plain,(
    ! [X7] : r1_xboole_0(X7,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_17,plain,(
    ! [X10,X11] :
      ( ~ r1_xboole_0(k1_tarski(X10),X11)
      | ~ r2_hidden(X10,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_18,plain,(
    ! [X37,X38,X39] :
      ( ~ v1_relat_1(X39)
      | ~ r1_xboole_0(X37,X38)
      | k7_relat_1(k7_relat_1(X39,X37),X38) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).

fof(c_0_19,plain,(
    ! [X31] :
      ( ~ v1_relat_1(X31)
      | k7_relat_1(X31,k1_xboole_0) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_relat_1])])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X12,X13,X16,X18,X19] :
      ( ( ~ v1_relat_1(X12)
        | ~ r2_hidden(X13,X12)
        | X13 = k4_tarski(esk1_2(X12,X13),esk2_2(X12,X13)) )
      & ( r2_hidden(esk3_1(X16),X16)
        | v1_relat_1(X16) )
      & ( esk3_1(X16) != k4_tarski(X18,X19)
        | v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

cnf(c_0_24,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k7_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X45,X46] :
      ( ~ v1_relat_1(X46)
      | ~ r1_tarski(X45,k1_relat_1(X46))
      | k1_relat_1(k7_relat_1(X46,X45)) = X45 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

cnf(c_0_30,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_31,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_32,plain,(
    ! [X20,X21,X22,X23,X24] :
      ( ( ~ r1_tarski(X20,X21)
        | ~ r2_hidden(k4_tarski(X22,X23),X20)
        | r2_hidden(k4_tarski(X22,X23),X21)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(esk4_2(X20,X24),esk5_2(X20,X24)),X20)
        | r1_tarski(X20,X24)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(esk4_2(X20,X24),esk5_2(X20,X24)),X24)
        | r1_tarski(X20,X24)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

fof(c_0_33,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r1_xboole_0(X1,X2)
            & v2_funct_1(X3) )
         => r1_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t125_funct_1])).

fof(c_0_34,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | k2_relat_1(k7_relat_1(X33,X32)) = k9_relat_1(X33,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_35,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_38,negated_conjecture,
    ( v1_relat_1(esk11_0)
    & v1_funct_1(esk11_0)
    & r1_xboole_0(esk9_0,esk10_0)
    & v2_funct_1(esk11_0)
    & ~ r1_xboole_0(k9_relat_1(esk11_0,esk9_0),k9_relat_1(esk11_0,esk10_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).

fof(c_0_39,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X35)
      | ~ r2_hidden(X34,k2_relat_1(X35))
      | r2_hidden(esk6_2(X34,X35),k1_relat_1(X35)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_relat_1])])])])).

cnf(c_0_40,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( k1_relat_1(k1_xboole_0) = X1
    | ~ r1_tarski(X1,k1_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_31])])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_31]),c_0_27])).

cnf(c_0_43,plain,
    ( k7_relat_1(X1,k7_relat_1(k7_relat_1(X2,X3),X4)) = k7_relat_1(k7_relat_1(X2,X3),X4)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_xboole_0(X3,X4) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_44,plain,
    ( r1_xboole_0(k7_relat_1(k7_relat_1(X1,X2),X3),X4)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( r1_xboole_0(esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( r2_hidden(esk6_2(X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_36]),c_0_31])])).

cnf(c_0_48,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3),X4) = k1_xboole_0
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_43]),c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(esk10_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_45])).

fof(c_0_51,plain,(
    ! [X42] :
      ( ~ v1_relat_1(X42)
      | r2_hidden(k4_tarski(esk7_1(X42),esk8_1(X42)),X42)
      | X42 = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X2)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_31])]),c_0_48]),c_0_27])).

fof(c_0_53,plain,(
    ! [X48,X49,X50] :
      ( ~ v1_relat_1(X50)
      | ~ v1_funct_1(X50)
      | ~ v2_funct_1(X50)
      | k9_relat_1(X50,k3_xboole_0(X48,X49)) = k3_xboole_0(k9_relat_1(X50,X48),k9_relat_1(X50,X49)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_1])])).

fof(c_0_54,plain,(
    ! [X28,X29,X30] :
      ( ~ v1_relat_1(X30)
      | k7_relat_1(k7_relat_1(X30,X28),X29) = k7_relat_1(X30,k3_xboole_0(X28,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

cnf(c_0_55,negated_conjecture,
    ( k7_relat_1(k7_relat_1(k7_relat_1(X1,esk10_0),esk9_0),X2) = k1_xboole_0
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_57,plain,
    ( r2_hidden(k4_tarski(esk7_1(X1),esk8_1(X1)),X1)
    | X1 = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( v1_relat_1(k9_relat_1(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_28])).

fof(c_0_59,plain,(
    ! [X8,X9] :
      ( r1_xboole_0(X8,X9)
      | ~ r1_xboole_0(k3_xboole_0(X8,X9),X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t75_xboole_1])])])).

cnf(c_0_60,plain,
    ( k9_relat_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( v2_funct_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_63,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3),X4) = k7_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_24])).

cnf(c_0_65,negated_conjecture,
    ( k7_relat_1(k7_relat_1(k7_relat_1(X1,esk10_0),esk9_0),X2) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_66,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_52])).

cnf(c_0_67,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k3_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( k3_xboole_0(k9_relat_1(esk11_0,X1),k9_relat_1(esk11_0,X2)) = k9_relat_1(esk11_0,k3_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_56])])).

cnf(c_0_69,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(X1,esk10_0),esk9_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_50])])).

cnf(c_0_71,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_47,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( r1_xboole_0(k9_relat_1(esk11_0,X1),k9_relat_1(esk11_0,X2))
    | ~ r1_xboole_0(k9_relat_1(esk11_0,k3_xboole_0(X1,X2)),k9_relat_1(esk11_0,X2)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( k9_relat_1(X1,k3_xboole_0(esk10_0,esk9_0)) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( r1_xboole_0(k9_relat_1(esk11_0,esk10_0),k9_relat_1(esk11_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_26]),c_0_56])])).

cnf(c_0_75,negated_conjecture,
    ( ~ r1_xboole_0(k9_relat_1(esk11_0,esk9_0),k9_relat_1(esk11_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_74]),c_0_75]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:28:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.46/0.64  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.46/0.64  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.46/0.64  #
% 0.46/0.64  # Preprocessing time       : 0.028 s
% 0.46/0.64  # Presaturation interreduction done
% 0.46/0.64  
% 0.46/0.64  # Proof found!
% 0.46/0.64  # SZS status Theorem
% 0.46/0.64  # SZS output start CNFRefutation
% 0.46/0.64  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.46/0.64  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.46/0.64  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.46/0.64  fof(t207_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_xboole_0(X1,X2)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 0.46/0.64  fof(t110_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 0.46/0.64  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 0.46/0.64  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 0.46/0.64  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 0.46/0.64  fof(t125_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_xboole_0(X1,X2)&v2_funct_1(X3))=>r1_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_funct_1)).
% 0.46/0.64  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.46/0.64  fof(t19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>~((r2_hidden(X1,k2_relat_1(X2))&![X3]:~(r2_hidden(X3,k1_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relat_1)).
% 0.46/0.64  fof(t56_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(![X2, X3]:~(r2_hidden(k4_tarski(X2,X3),X1))=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 0.46/0.64  fof(t121_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k3_xboole_0(X1,X2))=k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 0.46/0.64  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 0.46/0.64  fof(t75_xboole_1, axiom, ![X1, X2]:~((~(r1_xboole_0(X1,X2))&r1_xboole_0(k3_xboole_0(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 0.46/0.64  fof(c_0_15, plain, ![X5, X6]:(~r1_xboole_0(X5,X6)|r1_xboole_0(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.46/0.64  fof(c_0_16, plain, ![X7]:r1_xboole_0(X7,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.46/0.64  fof(c_0_17, plain, ![X10, X11]:(~r1_xboole_0(k1_tarski(X10),X11)|~r2_hidden(X10,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.46/0.64  fof(c_0_18, plain, ![X37, X38, X39]:(~v1_relat_1(X39)|(~r1_xboole_0(X37,X38)|k7_relat_1(k7_relat_1(X39,X37),X38)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).
% 0.46/0.64  fof(c_0_19, plain, ![X31]:(~v1_relat_1(X31)|k7_relat_1(X31,k1_xboole_0)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_relat_1])])).
% 0.46/0.64  cnf(c_0_20, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.46/0.64  cnf(c_0_21, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.46/0.64  cnf(c_0_22, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.46/0.64  fof(c_0_23, plain, ![X12, X13, X16, X18, X19]:((~v1_relat_1(X12)|(~r2_hidden(X13,X12)|X13=k4_tarski(esk1_2(X12,X13),esk2_2(X12,X13))))&((r2_hidden(esk3_1(X16),X16)|v1_relat_1(X16))&(esk3_1(X16)!=k4_tarski(X18,X19)|v1_relat_1(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.46/0.64  cnf(c_0_24, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.46/0.64  cnf(c_0_25, plain, (k7_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.46/0.64  cnf(c_0_26, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.46/0.64  cnf(c_0_27, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 0.46/0.64  cnf(c_0_28, plain, (r2_hidden(esk3_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.46/0.64  fof(c_0_29, plain, ![X45, X46]:(~v1_relat_1(X46)|(~r1_tarski(X45,k1_relat_1(X46))|k1_relat_1(k7_relat_1(X46,X45))=X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.46/0.64  cnf(c_0_30, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.46/0.64  cnf(c_0_31, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.46/0.64  fof(c_0_32, plain, ![X20, X21, X22, X23, X24]:((~r1_tarski(X20,X21)|(~r2_hidden(k4_tarski(X22,X23),X20)|r2_hidden(k4_tarski(X22,X23),X21))|~v1_relat_1(X20))&((r2_hidden(k4_tarski(esk4_2(X20,X24),esk5_2(X20,X24)),X20)|r1_tarski(X20,X24)|~v1_relat_1(X20))&(~r2_hidden(k4_tarski(esk4_2(X20,X24),esk5_2(X20,X24)),X24)|r1_tarski(X20,X24)|~v1_relat_1(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.46/0.64  fof(c_0_33, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_xboole_0(X1,X2)&v2_funct_1(X3))=>r1_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t125_funct_1])).
% 0.46/0.64  fof(c_0_34, plain, ![X32, X33]:(~v1_relat_1(X33)|k2_relat_1(k7_relat_1(X33,X32))=k9_relat_1(X33,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.46/0.64  cnf(c_0_35, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.46/0.64  cnf(c_0_36, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.46/0.64  cnf(c_0_37, plain, (r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.46/0.64  fof(c_0_38, negated_conjecture, ((v1_relat_1(esk11_0)&v1_funct_1(esk11_0))&((r1_xboole_0(esk9_0,esk10_0)&v2_funct_1(esk11_0))&~r1_xboole_0(k9_relat_1(esk11_0,esk9_0),k9_relat_1(esk11_0,esk10_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).
% 0.46/0.64  fof(c_0_39, plain, ![X34, X35]:(~v1_relat_1(X35)|(~r2_hidden(X34,k2_relat_1(X35))|r2_hidden(esk6_2(X34,X35),k1_relat_1(X35)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_relat_1])])])])).
% 0.46/0.64  cnf(c_0_40, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.46/0.64  cnf(c_0_41, plain, (k1_relat_1(k1_xboole_0)=X1|~r1_tarski(X1,k1_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_31])])).
% 0.46/0.64  cnf(c_0_42, plain, (r1_tarski(k1_xboole_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_31]), c_0_27])).
% 0.46/0.64  cnf(c_0_43, plain, (k7_relat_1(X1,k7_relat_1(k7_relat_1(X2,X3),X4))=k7_relat_1(k7_relat_1(X2,X3),X4)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_xboole_0(X3,X4)), inference(spm,[status(thm)],[c_0_25, c_0_24])).
% 0.46/0.64  cnf(c_0_44, plain, (r1_xboole_0(k7_relat_1(k7_relat_1(X1,X2),X3),X4)|~v1_relat_1(X1)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 0.46/0.64  cnf(c_0_45, negated_conjecture, (r1_xboole_0(esk9_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.46/0.64  cnf(c_0_46, plain, (r2_hidden(esk6_2(X2,X1),k1_relat_1(X1))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.46/0.64  cnf(c_0_47, plain, (k2_relat_1(k1_xboole_0)=k9_relat_1(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_36]), c_0_31])])).
% 0.46/0.64  cnf(c_0_48, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.46/0.64  cnf(c_0_49, plain, (k7_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3),X4)=k1_xboole_0|~v1_relat_1(X5)|~v1_relat_1(X1)|~r1_xboole_0(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_43]), c_0_44])).
% 0.46/0.64  cnf(c_0_50, negated_conjecture, (r1_xboole_0(esk10_0,esk9_0)), inference(spm,[status(thm)],[c_0_20, c_0_45])).
% 0.46/0.64  fof(c_0_51, plain, ![X42]:(~v1_relat_1(X42)|(r2_hidden(k4_tarski(esk7_1(X42),esk8_1(X42)),X42)|X42=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).
% 0.46/0.64  cnf(c_0_52, plain, (~r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_31])]), c_0_48]), c_0_27])).
% 0.46/0.64  fof(c_0_53, plain, ![X48, X49, X50]:(~v1_relat_1(X50)|~v1_funct_1(X50)|(~v2_funct_1(X50)|k9_relat_1(X50,k3_xboole_0(X48,X49))=k3_xboole_0(k9_relat_1(X50,X48),k9_relat_1(X50,X49)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_1])])).
% 0.46/0.64  fof(c_0_54, plain, ![X28, X29, X30]:(~v1_relat_1(X30)|k7_relat_1(k7_relat_1(X30,X28),X29)=k7_relat_1(X30,k3_xboole_0(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.46/0.64  cnf(c_0_55, negated_conjecture, (k7_relat_1(k7_relat_1(k7_relat_1(X1,esk10_0),esk9_0),X2)=k1_xboole_0|~v1_relat_1(X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.46/0.64  cnf(c_0_56, negated_conjecture, (v1_relat_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.46/0.64  cnf(c_0_57, plain, (r2_hidden(k4_tarski(esk7_1(X1),esk8_1(X1)),X1)|X1=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.46/0.64  cnf(c_0_58, plain, (v1_relat_1(k9_relat_1(k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_52, c_0_28])).
% 0.46/0.64  fof(c_0_59, plain, ![X8, X9]:(r1_xboole_0(X8,X9)|~r1_xboole_0(k3_xboole_0(X8,X9),X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t75_xboole_1])])])).
% 0.46/0.64  cnf(c_0_60, plain, (k9_relat_1(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.46/0.64  cnf(c_0_61, negated_conjecture, (v2_funct_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.46/0.64  cnf(c_0_62, negated_conjecture, (v1_funct_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.46/0.64  cnf(c_0_63, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.46/0.64  cnf(c_0_64, plain, (k7_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3),X4)=k7_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(X1)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_36, c_0_24])).
% 0.46/0.64  cnf(c_0_65, negated_conjecture, (k7_relat_1(k7_relat_1(k7_relat_1(X1,esk10_0),esk9_0),X2)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.46/0.64  cnf(c_0_66, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_52])).
% 0.46/0.64  cnf(c_0_67, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k3_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.46/0.64  cnf(c_0_68, negated_conjecture, (k3_xboole_0(k9_relat_1(esk11_0,X1),k9_relat_1(esk11_0,X2))=k9_relat_1(esk11_0,k3_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_56])])).
% 0.46/0.64  cnf(c_0_69, plain, (k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))=k9_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_40, c_0_63])).
% 0.46/0.64  cnf(c_0_70, negated_conjecture, (k1_xboole_0=k7_relat_1(k7_relat_1(X1,esk10_0),esk9_0)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_50])])).
% 0.46/0.64  cnf(c_0_71, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_47, c_0_66])).
% 0.46/0.64  cnf(c_0_72, negated_conjecture, (r1_xboole_0(k9_relat_1(esk11_0,X1),k9_relat_1(esk11_0,X2))|~r1_xboole_0(k9_relat_1(esk11_0,k3_xboole_0(X1,X2)),k9_relat_1(esk11_0,X2))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.46/0.64  cnf(c_0_73, negated_conjecture, (k9_relat_1(X1,k3_xboole_0(esk10_0,esk9_0))=k1_xboole_0|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])).
% 0.46/0.64  cnf(c_0_74, negated_conjecture, (r1_xboole_0(k9_relat_1(esk11_0,esk10_0),k9_relat_1(esk11_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_26]), c_0_56])])).
% 0.46/0.64  cnf(c_0_75, negated_conjecture, (~r1_xboole_0(k9_relat_1(esk11_0,esk9_0),k9_relat_1(esk11_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.46/0.64  cnf(c_0_76, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_74]), c_0_75]), ['proof']).
% 0.46/0.64  # SZS output end CNFRefutation
% 0.46/0.64  # Proof object total steps             : 77
% 0.46/0.64  # Proof object clause steps            : 46
% 0.46/0.64  # Proof object formula steps           : 31
% 0.46/0.64  # Proof object conjectures             : 17
% 0.46/0.64  # Proof object clause conjectures      : 14
% 0.46/0.64  # Proof object formula conjectures     : 3
% 0.46/0.64  # Proof object initial clauses used    : 19
% 0.46/0.64  # Proof object initial formulas used   : 15
% 0.46/0.64  # Proof object generating inferences   : 26
% 0.46/0.64  # Proof object simplifying inferences  : 24
% 0.46/0.64  # Training examples: 0 positive, 0 negative
% 0.46/0.64  # Parsed axioms                        : 18
% 0.46/0.64  # Removed by relevancy pruning/SinE    : 0
% 0.46/0.64  # Initial clauses                      : 28
% 0.46/0.64  # Removed in clause preprocessing      : 0
% 0.46/0.64  # Initial clauses in saturation        : 28
% 0.46/0.64  # Processed clauses                    : 3203
% 0.46/0.64  # ...of these trivial                  : 20
% 0.46/0.64  # ...subsumed                          : 2634
% 0.46/0.64  # ...remaining for further processing  : 549
% 0.46/0.64  # Other redundant clauses eliminated   : 1
% 0.46/0.64  # Clauses deleted for lack of memory   : 0
% 0.46/0.64  # Backward-subsumed                    : 29
% 0.46/0.64  # Backward-rewritten                   : 83
% 0.46/0.64  # Generated clauses                    : 23845
% 0.46/0.64  # ...of the previous two non-trivial   : 19147
% 0.46/0.64  # Contextual simplify-reflections      : 19
% 0.46/0.64  # Paramodulations                      : 23844
% 0.46/0.64  # Factorizations                       : 0
% 0.46/0.64  # Equation resolutions                 : 1
% 0.46/0.64  # Propositional unsat checks           : 0
% 0.46/0.64  #    Propositional check models        : 0
% 0.46/0.64  #    Propositional check unsatisfiable : 0
% 0.46/0.64  #    Propositional clauses             : 0
% 0.46/0.64  #    Propositional clauses after purity: 0
% 0.46/0.64  #    Propositional unsat core size     : 0
% 0.46/0.64  #    Propositional preprocessing time  : 0.000
% 0.46/0.64  #    Propositional encoding time       : 0.000
% 0.46/0.64  #    Propositional solver time         : 0.000
% 0.46/0.64  #    Success case prop preproc time    : 0.000
% 0.46/0.64  #    Success case prop encoding time   : 0.000
% 0.46/0.64  #    Success case prop solver time     : 0.000
% 0.46/0.64  # Current number of processed clauses  : 410
% 0.46/0.64  #    Positive orientable unit clauses  : 67
% 0.46/0.64  #    Positive unorientable unit clauses: 0
% 0.46/0.64  #    Negative unit clauses             : 9
% 0.46/0.64  #    Non-unit-clauses                  : 334
% 0.46/0.64  # Current number of unprocessed clauses: 15802
% 0.46/0.64  # ...number of literals in the above   : 82377
% 0.46/0.64  # Current number of archived formulas  : 0
% 0.46/0.64  # Current number of archived clauses   : 139
% 0.46/0.64  # Clause-clause subsumption calls (NU) : 22397
% 0.46/0.64  # Rec. Clause-clause subsumption calls : 11299
% 0.46/0.64  # Non-unit clause-clause subsumptions  : 1085
% 0.46/0.64  # Unit Clause-clause subsumption calls : 201
% 0.46/0.64  # Rewrite failures with RHS unbound    : 16
% 0.46/0.64  # BW rewrite match attempts            : 172
% 0.46/0.64  # BW rewrite match successes           : 31
% 0.46/0.64  # Condensation attempts                : 0
% 0.46/0.64  # Condensation successes               : 0
% 0.46/0.64  # Termbank termtop insertions          : 353525
% 0.46/0.64  
% 0.46/0.64  # -------------------------------------------------
% 0.46/0.64  # User time                : 0.279 s
% 0.46/0.64  # System time              : 0.015 s
% 0.46/0.64  # Total time               : 0.295 s
% 0.46/0.64  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
