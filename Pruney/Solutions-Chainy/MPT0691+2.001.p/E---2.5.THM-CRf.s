%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:41 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 206 expanded)
%              Number of clauses        :   45 (  92 expanded)
%              Number of leaves         :   19 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :  212 ( 649 expanded)
%              Number of equality atoms :   67 ( 224 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(t9_tarski,axiom,(
    ! [X1] :
    ? [X2] :
      ( r2_hidden(X1,X2)
      & ! [X3,X4] :
          ( ( r2_hidden(X3,X2)
            & r1_tarski(X4,X3) )
         => r2_hidden(X4,X2) )
      & ! [X3] :
          ~ ( r2_hidden(X3,X2)
            & ! [X4] :
                ~ ( r2_hidden(X4,X2)
                  & ! [X5] :
                      ( r1_tarski(X5,X3)
                     => r2_hidden(X5,X4) ) ) )
      & ! [X3] :
          ~ ( r1_tarski(X3,X2)
            & ~ r2_tarski(X3,X2)
            & ~ r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tarski)).

fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

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

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t146_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(t162_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(c_0_19,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X13,X12)
        | r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X12 != k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X14,X10)
        | r2_hidden(X14,X12)
        | X12 != k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X12 != k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X15,X16,X17),X15)
        | ~ r2_hidden(esk1_3(X15,X16,X17),X17)
        | X17 = k2_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk1_3(X15,X16,X17),X16)
        | ~ r2_hidden(esk1_3(X15,X16,X17),X17)
        | X17 = k2_xboole_0(X15,X16) )
      & ( r2_hidden(esk1_3(X15,X16,X17),X17)
        | r2_hidden(esk1_3(X15,X16,X17),X15)
        | r2_hidden(esk1_3(X15,X16,X17),X16)
        | X17 = k2_xboole_0(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_20,plain,(
    ! [X27,X28] : k3_tarski(k2_tarski(X27,X28)) = k2_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | ~ r2_hidden(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

fof(c_0_22,plain,(
    ! [X29,X31,X32,X33,X35,X36] :
      ( r2_hidden(X29,esk2_1(X29))
      & ( ~ r2_hidden(X31,esk2_1(X29))
        | ~ r1_tarski(X32,X31)
        | r2_hidden(X32,esk2_1(X29)) )
      & ( r2_hidden(esk3_2(X29,X33),esk2_1(X29))
        | ~ r2_hidden(X33,esk2_1(X29)) )
      & ( ~ r1_tarski(X35,X33)
        | r2_hidden(X35,esk3_2(X29,X33))
        | ~ r2_hidden(X33,esk2_1(X29)) )
      & ( ~ r1_tarski(X36,esk2_1(X29))
        | r2_tarski(X36,esk2_1(X29))
        | r2_hidden(X36,esk2_1(X29)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_tarski])])])])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k2_tarski(X2,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_28,plain,(
    ! [X25,X26] :
      ( ~ r1_tarski(X25,X26)
      | X26 = k2_xboole_0(X25,k4_xboole_0(X26,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

fof(c_0_29,plain,(
    ! [X46,X47] :
      ( ~ v1_relat_1(X47)
      | k1_relat_1(k7_relat_1(X47,X46)) = k3_xboole_0(k1_relat_1(X47),X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_30,plain,(
    ! [X53,X54] :
      ( ( v1_relat_1(esk4_2(X53,X54))
        | X53 = k1_xboole_0 )
      & ( v1_funct_1(esk4_2(X53,X54))
        | X53 = k1_xboole_0 )
      & ( X54 = k1_relat_1(esk4_2(X53,X54))
        | X53 = k1_xboole_0 )
      & ( r1_tarski(k2_relat_1(esk4_2(X53,X54)),X53)
        | X53 = k1_xboole_0 )
      & ( v1_relat_1(esk4_2(X53,X54))
        | X54 != k1_xboole_0 )
      & ( v1_funct_1(esk4_2(X53,X54))
        | X54 != k1_xboole_0 )
      & ( X54 = k1_relat_1(esk4_2(X53,X54))
        | X54 != k1_xboole_0 )
      & ( r1_tarski(k2_relat_1(esk4_2(X53,X54)),X53)
        | X54 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_funct_1])])])])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(esk2_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( X1 = k1_relat_1(esk4_2(X2,X1))
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( v1_relat_1(esk4_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_37,plain,(
    ! [X48,X49] :
      ( ~ v1_relat_1(X49)
      | ~ r1_tarski(k1_relat_1(X49),X48)
      | k7_relat_1(X49,X48) = X49 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(esk2_1(k3_tarski(k2_tarski(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( X2 = k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X1)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_24])).

fof(c_0_40,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,X20)
      | r1_tarski(X19,k2_xboole_0(X21,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_41,plain,
    ( k1_relat_1(k7_relat_1(esk4_2(X1,X2),X3)) = k3_xboole_0(X2,X3)
    | X1 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_42,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_43,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k1_relat_1(X2))
         => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t146_funct_1])).

cnf(c_0_44,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( k1_relat_1(esk4_2(X1,X2)) = k3_xboole_0(X2,X3)
    | X1 = k1_xboole_0
    | ~ r1_tarski(k1_relat_1(esk4_2(X1,X2)),X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_36])).

fof(c_0_47,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & r1_tarski(esk5_0,k1_relat_1(esk6_0))
    & ~ r1_tarski(esk5_0,k10_relat_1(esk6_0,k9_relat_1(esk6_0,esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).

fof(c_0_48,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_49,plain,
    ( ~ r1_tarski(esk2_1(esk2_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_26])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_45,c_0_24])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X2) = X1
    | X3 = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_35])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk5_0,k1_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_53,plain,(
    ! [X24] : r1_tarski(k1_xboole_0,X24) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_54,plain,(
    ! [X39] :
      ( ~ v1_relat_1(X39)
      | k9_relat_1(X39,k1_relat_1(X39)) = k2_relat_1(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

fof(c_0_55,plain,(
    ! [X40,X41,X42] :
      ( ~ v1_relat_1(X40)
      | ~ r1_tarski(X41,X42)
      | k9_relat_1(k7_relat_1(X40,X42),X41) = k9_relat_1(X40,X41) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).

fof(c_0_56,plain,(
    ! [X44,X45] :
      ( ~ v1_relat_1(X45)
      | r1_tarski(k1_relat_1(k7_relat_1(X45,X44)),X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

fof(c_0_57,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X37)
      | v1_relat_1(k7_relat_1(X37,X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,plain,
    ( ~ r1_tarski(esk2_1(esk2_1(k3_tarski(k2_tarski(X1,X2)))),X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( k3_xboole_0(esk5_0,k1_relat_1(esk6_0)) = esk5_0
    | X1 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_62,plain,(
    ! [X22,X23] : r1_tarski(k3_xboole_0(X22,X23),X22) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_63,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,k1_relat_1(X2)) = k1_relat_1(k7_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_34])).

cnf(c_0_68,negated_conjecture,
    ( k3_xboole_0(esk5_0,k1_relat_1(esk6_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])])).

cnf(c_0_69,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_70,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_71,plain,(
    ! [X50,X51,X52] :
      ( ~ v1_relat_1(X52)
      | k10_relat_1(k7_relat_1(X52,X50),X51) = k3_xboole_0(X50,k10_relat_1(X52,X51)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

fof(c_0_72,plain,(
    ! [X43] :
      ( ~ v1_relat_1(X43)
      | k10_relat_1(X43,k2_relat_1(X43)) = k1_relat_1(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_73,plain,
    ( k9_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2))) = k2_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk6_0,esk5_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])])).

cnf(c_0_75,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_58])).

cnf(c_0_76,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_77,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk6_0,esk5_0)) = k9_relat_1(esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_69])])).

cnf(c_0_79,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(X1,X2),X3),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk6_0,esk5_0),k9_relat_1(esk6_0,esk5_0)) = esk5_0
    | ~ v1_relat_1(k7_relat_1(esk6_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k10_relat_1(esk6_0,k9_relat_1(esk6_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_82,negated_conjecture,
    ( ~ v1_relat_1(k7_relat_1(esk6_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_69])]),c_0_81])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_66]),c_0_69])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.78/0.98  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.78/0.98  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.78/0.98  #
% 0.78/0.98  # Preprocessing time       : 0.028 s
% 0.78/0.98  # Presaturation interreduction done
% 0.78/0.98  
% 0.78/0.98  # Proof found!
% 0.78/0.98  # SZS status Theorem
% 0.78/0.98  # SZS output start CNFRefutation
% 0.78/0.98  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.78/0.98  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.78/0.98  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.78/0.98  fof(t9_tarski, axiom, ![X1]:?[X2]:(((r2_hidden(X1,X2)&![X3, X4]:((r2_hidden(X3,X2)&r1_tarski(X4,X3))=>r2_hidden(X4,X2)))&![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X2)&![X5]:(r1_tarski(X5,X3)=>r2_hidden(X5,X4)))))))&![X3]:~(((r1_tarski(X3,X2)&~(r2_tarski(X3,X2)))&~(r2_hidden(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_tarski)).
% 0.78/0.98  fof(t45_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 0.78/0.98  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 0.78/0.98  fof(t18_funct_1, axiom, ![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 0.78/0.98  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 0.78/0.98  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.78/0.98  fof(t146_funct_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.78/0.98  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.78/0.98  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.78/0.98  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.78/0.98  fof(t162_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 0.78/0.98  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.78/0.98  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.78/0.98  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.78/0.98  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 0.78/0.98  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.78/0.98  fof(c_0_19, plain, ![X10, X11, X12, X13, X14, X15, X16, X17]:(((~r2_hidden(X13,X12)|(r2_hidden(X13,X10)|r2_hidden(X13,X11))|X12!=k2_xboole_0(X10,X11))&((~r2_hidden(X14,X10)|r2_hidden(X14,X12)|X12!=k2_xboole_0(X10,X11))&(~r2_hidden(X14,X11)|r2_hidden(X14,X12)|X12!=k2_xboole_0(X10,X11))))&(((~r2_hidden(esk1_3(X15,X16,X17),X15)|~r2_hidden(esk1_3(X15,X16,X17),X17)|X17=k2_xboole_0(X15,X16))&(~r2_hidden(esk1_3(X15,X16,X17),X16)|~r2_hidden(esk1_3(X15,X16,X17),X17)|X17=k2_xboole_0(X15,X16)))&(r2_hidden(esk1_3(X15,X16,X17),X17)|(r2_hidden(esk1_3(X15,X16,X17),X15)|r2_hidden(esk1_3(X15,X16,X17),X16))|X17=k2_xboole_0(X15,X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.78/0.98  fof(c_0_20, plain, ![X27, X28]:k3_tarski(k2_tarski(X27,X28))=k2_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.78/0.98  fof(c_0_21, plain, ![X6, X7]:(~r2_hidden(X6,X7)|~r2_hidden(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.78/0.98  fof(c_0_22, plain, ![X29, X31, X32, X33, X35, X36]:(((r2_hidden(X29,esk2_1(X29))&(~r2_hidden(X31,esk2_1(X29))|~r1_tarski(X32,X31)|r2_hidden(X32,esk2_1(X29))))&((r2_hidden(esk3_2(X29,X33),esk2_1(X29))|~r2_hidden(X33,esk2_1(X29)))&(~r1_tarski(X35,X33)|r2_hidden(X35,esk3_2(X29,X33))|~r2_hidden(X33,esk2_1(X29)))))&(~r1_tarski(X36,esk2_1(X29))|r2_tarski(X36,esk2_1(X29))|r2_hidden(X36,esk2_1(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_tarski])])])])])])).
% 0.78/0.98  cnf(c_0_23, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.78/0.98  cnf(c_0_24, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.78/0.98  cnf(c_0_25, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.78/0.98  cnf(c_0_26, plain, (r2_hidden(X1,esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.78/0.98  cnf(c_0_27, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k2_tarski(X2,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.78/0.98  fof(c_0_28, plain, ![X25, X26]:(~r1_tarski(X25,X26)|X26=k2_xboole_0(X25,k4_xboole_0(X26,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).
% 0.78/0.98  fof(c_0_29, plain, ![X46, X47]:(~v1_relat_1(X47)|k1_relat_1(k7_relat_1(X47,X46))=k3_xboole_0(k1_relat_1(X47),X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.78/0.98  fof(c_0_30, plain, ![X53, X54]:((((v1_relat_1(esk4_2(X53,X54))|X53=k1_xboole_0)&(v1_funct_1(esk4_2(X53,X54))|X53=k1_xboole_0))&((X54=k1_relat_1(esk4_2(X53,X54))|X53=k1_xboole_0)&(r1_tarski(k2_relat_1(esk4_2(X53,X54)),X53)|X53=k1_xboole_0)))&(((v1_relat_1(esk4_2(X53,X54))|X54!=k1_xboole_0)&(v1_funct_1(esk4_2(X53,X54))|X54!=k1_xboole_0))&((X54=k1_relat_1(esk4_2(X53,X54))|X54!=k1_xboole_0)&(r1_tarski(k2_relat_1(esk4_2(X53,X54)),X53)|X54!=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_funct_1])])])])).
% 0.78/0.98  cnf(c_0_31, plain, (~r2_hidden(esk2_1(X1),X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.78/0.98  cnf(c_0_32, plain, (r2_hidden(X1,k3_tarski(k2_tarski(X2,X3)))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_27])).
% 0.78/0.98  cnf(c_0_33, plain, (X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.78/0.98  cnf(c_0_34, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.78/0.98  cnf(c_0_35, plain, (X1=k1_relat_1(esk4_2(X2,X1))|X2=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.78/0.98  cnf(c_0_36, plain, (v1_relat_1(esk4_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.78/0.98  fof(c_0_37, plain, ![X48, X49]:(~v1_relat_1(X49)|(~r1_tarski(k1_relat_1(X49),X48)|k7_relat_1(X49,X48)=X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.78/0.98  cnf(c_0_38, plain, (~r2_hidden(esk2_1(k3_tarski(k2_tarski(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.78/0.98  cnf(c_0_39, plain, (X2=k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X1)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_24])).
% 0.78/0.98  fof(c_0_40, plain, ![X19, X20, X21]:(~r1_tarski(X19,X20)|r1_tarski(X19,k2_xboole_0(X21,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.78/0.98  cnf(c_0_41, plain, (k1_relat_1(k7_relat_1(esk4_2(X1,X2),X3))=k3_xboole_0(X2,X3)|X1=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.78/0.98  cnf(c_0_42, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.78/0.98  fof(c_0_43, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t146_funct_1])).
% 0.78/0.98  cnf(c_0_44, plain, (~r1_tarski(X1,X2)|~r2_hidden(esk2_1(X2),X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.78/0.98  cnf(c_0_45, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.78/0.98  cnf(c_0_46, plain, (k1_relat_1(esk4_2(X1,X2))=k3_xboole_0(X2,X3)|X1=k1_xboole_0|~r1_tarski(k1_relat_1(esk4_2(X1,X2)),X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_36])).
% 0.78/0.98  fof(c_0_47, negated_conjecture, (v1_relat_1(esk6_0)&(r1_tarski(esk5_0,k1_relat_1(esk6_0))&~r1_tarski(esk5_0,k10_relat_1(esk6_0,k9_relat_1(esk6_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).
% 0.78/0.98  fof(c_0_48, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.78/0.98  cnf(c_0_49, plain, (~r1_tarski(esk2_1(esk2_1(X1)),X1)), inference(spm,[status(thm)],[c_0_44, c_0_26])).
% 0.78/0.98  cnf(c_0_50, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_45, c_0_24])).
% 0.78/0.98  cnf(c_0_51, plain, (k3_xboole_0(X1,X2)=X1|X3=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_46, c_0_35])).
% 0.78/0.98  cnf(c_0_52, negated_conjecture, (r1_tarski(esk5_0,k1_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.78/0.98  fof(c_0_53, plain, ![X24]:r1_tarski(k1_xboole_0,X24), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.78/0.98  fof(c_0_54, plain, ![X39]:(~v1_relat_1(X39)|k9_relat_1(X39,k1_relat_1(X39))=k2_relat_1(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.78/0.98  fof(c_0_55, plain, ![X40, X41, X42]:(~v1_relat_1(X40)|(~r1_tarski(X41,X42)|k9_relat_1(k7_relat_1(X40,X42),X41)=k9_relat_1(X40,X41))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).
% 0.78/0.98  fof(c_0_56, plain, ![X44, X45]:(~v1_relat_1(X45)|r1_tarski(k1_relat_1(k7_relat_1(X45,X44)),X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.78/0.98  fof(c_0_57, plain, ![X37, X38]:(~v1_relat_1(X37)|v1_relat_1(k7_relat_1(X37,X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.78/0.98  cnf(c_0_58, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.78/0.98  cnf(c_0_59, plain, (~r1_tarski(esk2_1(esk2_1(k3_tarski(k2_tarski(X1,X2)))),X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.78/0.98  cnf(c_0_60, negated_conjecture, (k3_xboole_0(esk5_0,k1_relat_1(esk6_0))=esk5_0|X1=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.78/0.98  cnf(c_0_61, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.78/0.98  fof(c_0_62, plain, ![X22, X23]:r1_tarski(k3_xboole_0(X22,X23),X22), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.78/0.98  cnf(c_0_63, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.78/0.98  cnf(c_0_64, plain, (k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.78/0.98  cnf(c_0_65, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.78/0.98  cnf(c_0_66, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.78/0.98  cnf(c_0_67, plain, (k3_xboole_0(X1,k1_relat_1(X2))=k1_relat_1(k7_relat_1(X2,X1))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_58, c_0_34])).
% 0.78/0.98  cnf(c_0_68, negated_conjecture, (k3_xboole_0(esk5_0,k1_relat_1(esk6_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])])).
% 0.78/0.98  cnf(c_0_69, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.78/0.98  cnf(c_0_70, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.78/0.98  fof(c_0_71, plain, ![X50, X51, X52]:(~v1_relat_1(X52)|k10_relat_1(k7_relat_1(X52,X50),X51)=k3_xboole_0(X50,k10_relat_1(X52,X51))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.78/0.98  fof(c_0_72, plain, ![X43]:(~v1_relat_1(X43)|k10_relat_1(X43,k2_relat_1(X43))=k1_relat_1(X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.78/0.98  cnf(c_0_73, plain, (k9_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2)))=k2_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_66])).
% 0.78/0.98  cnf(c_0_74, negated_conjecture, (k1_relat_1(k7_relat_1(esk6_0,esk5_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])])).
% 0.78/0.98  cnf(c_0_75, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_70, c_0_58])).
% 0.78/0.98  cnf(c_0_76, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.78/0.98  cnf(c_0_77, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.78/0.98  cnf(c_0_78, negated_conjecture, (k2_relat_1(k7_relat_1(esk6_0,esk5_0))=k9_relat_1(esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_69])])).
% 0.78/0.98  cnf(c_0_79, plain, (r1_tarski(k10_relat_1(k7_relat_1(X1,X2),X3),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.78/0.98  cnf(c_0_80, negated_conjecture, (k10_relat_1(k7_relat_1(esk6_0,esk5_0),k9_relat_1(esk6_0,esk5_0))=esk5_0|~v1_relat_1(k7_relat_1(esk6_0,esk5_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_74])).
% 0.78/0.98  cnf(c_0_81, negated_conjecture, (~r1_tarski(esk5_0,k10_relat_1(esk6_0,k9_relat_1(esk6_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.78/0.98  cnf(c_0_82, negated_conjecture, (~v1_relat_1(k7_relat_1(esk6_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_69])]), c_0_81])).
% 0.78/0.98  cnf(c_0_83, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_66]), c_0_69])]), ['proof']).
% 0.78/0.98  # SZS output end CNFRefutation
% 0.78/0.98  # Proof object total steps             : 84
% 0.78/0.98  # Proof object clause steps            : 45
% 0.78/0.98  # Proof object formula steps           : 39
% 0.78/0.98  # Proof object conjectures             : 13
% 0.78/0.98  # Proof object clause conjectures      : 10
% 0.78/0.98  # Proof object formula conjectures     : 3
% 0.78/0.98  # Proof object initial clauses used    : 22
% 0.78/0.98  # Proof object initial formulas used   : 19
% 0.78/0.98  # Proof object generating inferences   : 19
% 0.78/0.98  # Proof object simplifying inferences  : 20
% 0.78/0.98  # Training examples: 0 positive, 0 negative
% 0.78/0.98  # Parsed axioms                        : 19
% 0.78/0.98  # Removed by relevancy pruning/SinE    : 0
% 0.78/0.98  # Initial clauses                      : 37
% 0.78/0.98  # Removed in clause preprocessing      : 1
% 0.78/0.98  # Initial clauses in saturation        : 36
% 0.78/0.98  # Processed clauses                    : 2648
% 0.78/0.98  # ...of these trivial                  : 15
% 0.78/0.98  # ...subsumed                          : 1519
% 0.78/0.98  # ...remaining for further processing  : 1114
% 0.78/0.98  # Other redundant clauses eliminated   : 11
% 0.78/0.98  # Clauses deleted for lack of memory   : 0
% 0.78/0.98  # Backward-subsumed                    : 21
% 0.78/0.98  # Backward-rewritten                   : 10
% 0.78/0.98  # Generated clauses                    : 32919
% 0.78/0.98  # ...of the previous two non-trivial   : 31654
% 0.78/0.98  # Contextual simplify-reflections      : 17
% 0.78/0.98  # Paramodulations                      : 32206
% 0.78/0.98  # Factorizations                       : 702
% 0.78/0.98  # Equation resolutions                 : 11
% 0.78/0.98  # Propositional unsat checks           : 0
% 0.78/0.98  #    Propositional check models        : 0
% 0.78/0.98  #    Propositional check unsatisfiable : 0
% 0.78/0.98  #    Propositional clauses             : 0
% 0.78/0.98  #    Propositional clauses after purity: 0
% 0.78/0.98  #    Propositional unsat core size     : 0
% 0.78/0.98  #    Propositional preprocessing time  : 0.000
% 0.78/0.98  #    Propositional encoding time       : 0.000
% 0.78/0.98  #    Propositional solver time         : 0.000
% 0.78/0.98  #    Success case prop preproc time    : 0.000
% 0.78/0.98  #    Success case prop encoding time   : 0.000
% 0.78/0.98  #    Success case prop solver time     : 0.000
% 0.78/0.98  # Current number of processed clauses  : 1040
% 0.78/0.98  #    Positive orientable unit clauses  : 26
% 0.78/0.98  #    Positive unorientable unit clauses: 1
% 0.78/0.98  #    Negative unit clauses             : 70
% 0.78/0.98  #    Non-unit-clauses                  : 943
% 0.78/0.98  # Current number of unprocessed clauses: 28278
% 0.78/0.98  # ...number of literals in the above   : 168878
% 0.78/0.98  # Current number of archived formulas  : 0
% 0.78/0.98  # Current number of archived clauses   : 68
% 0.78/0.98  # Clause-clause subsumption calls (NU) : 356304
% 0.78/0.98  # Rec. Clause-clause subsumption calls : 60662
% 0.78/0.98  # Non-unit clause-clause subsumptions  : 1248
% 0.78/0.98  # Unit Clause-clause subsumption calls : 9414
% 0.78/0.98  # Rewrite failures with RHS unbound    : 0
% 0.78/0.98  # BW rewrite match attempts            : 19
% 0.78/0.98  # BW rewrite match successes           : 18
% 0.78/0.98  # Condensation attempts                : 0
% 0.78/0.98  # Condensation successes               : 0
% 0.78/0.98  # Termbank termtop insertions          : 702339
% 0.78/0.98  
% 0.78/0.98  # -------------------------------------------------
% 0.78/0.98  # User time                : 0.631 s
% 0.78/0.98  # System time              : 0.014 s
% 0.78/0.98  # Total time               : 0.644 s
% 0.78/0.98  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
