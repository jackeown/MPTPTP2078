%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:31 EST 2020

% Result     : Theorem 7.58s
% Output     : CNFRefutation 7.58s
% Verified   : 
% Statistics : Number of formulae       :  110 (1054 expanded)
%              Number of clauses        :   67 ( 444 expanded)
%              Number of leaves         :   21 ( 301 expanded)
%              Depth                    :   16
%              Number of atoms          :  246 (1855 expanded)
%              Number of equality atoms :   83 ( 940 expanded)
%              Maximal formula depth    :   18 (   3 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t147_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

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

fof(t148_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => k9_relat_1(X2,k10_relat_1(X2,X1)) = k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(t175_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( r1_tarski(k10_relat_1(X1,X3),X2)
         => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

fof(c_0_21,plain,(
    ! [X48,X49] : k1_setfam_1(k2_tarski(X48,X49)) = k3_xboole_0(X48,X49) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_22,plain,(
    ! [X21,X22] : k1_enumset1(X21,X21,X22) = k2_tarski(X21,X22) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X66,X67] :
      ( ~ v1_relat_1(X67)
      | ~ v1_funct_1(X67)
      | ~ r1_tarski(X66,k2_relat_1(X67))
      | k9_relat_1(X67,k10_relat_1(X67,X66)) = X66 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).

fof(c_0_24,plain,(
    ! [X60] :
      ( v1_relat_1(k6_relat_1(X60))
      & v1_funct_1(k6_relat_1(X60)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_25,plain,(
    ! [X51] :
      ( k1_relat_1(k6_relat_1(X51)) = X51
      & k2_relat_1(k6_relat_1(X51)) = X51 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_26,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_27,plain,(
    ! [X50] :
      ( ~ v1_relat_1(X50)
      | k10_relat_1(X50,k2_relat_1(X50)) = k1_relat_1(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_28,plain,(
    ! [X61,X62,X63] :
      ( ~ v1_relat_1(X63)
      | k10_relat_1(k7_relat_1(X63,X61),X62) = k3_xboole_0(X61,k10_relat_1(X63,X62)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_29,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X23,X24,X25] : k2_enumset1(X23,X23,X24,X25) = k1_enumset1(X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_32,plain,(
    ! [X26,X27,X28,X29] : k3_enumset1(X26,X26,X27,X28,X29) = k2_enumset1(X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_33,plain,(
    ! [X30,X31,X32,X33,X34] : k4_enumset1(X30,X30,X31,X32,X33,X34) = k3_enumset1(X30,X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_34,plain,(
    ! [X35,X36,X37,X38,X39,X40] : k5_enumset1(X35,X35,X36,X37,X38,X39,X40) = k4_enumset1(X35,X36,X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_35,plain,(
    ! [X41,X42,X43,X44,X45,X46,X47] : k6_enumset1(X41,X41,X42,X43,X44,X45,X46,X47) = k5_enumset1(X41,X42,X43,X44,X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_36,plain,(
    ! [X68,X69] :
      ( ~ v1_relat_1(X69)
      | ~ v1_funct_1(X69)
      | k9_relat_1(X69,k10_relat_1(X69,X68)) = k3_xboole_0(X68,k9_relat_1(X69,k1_relat_1(X69))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).

cnf(c_0_37,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_44,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_45,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_46,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_48,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_51,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_52,plain,
    ( k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_54,plain,
    ( k10_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_38]),c_0_40]),c_0_43])).

cnf(c_0_55,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50])).

fof(c_0_56,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2,X3] :
            ( r1_tarski(k10_relat_1(X1,X3),X2)
           => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t175_funct_2])).

fof(c_0_57,plain,(
    ! [X64,X65] :
      ( ~ v1_relat_1(X65)
      | ~ v1_funct_1(X65)
      | r1_tarski(k9_relat_1(X65,k10_relat_1(X65,X64)),X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_58,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k9_relat_1(X1,k1_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_59,plain,
    ( k9_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_60,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(k6_relat_1(X2),X3))) = k10_relat_1(k7_relat_1(k6_relat_1(X2),X1),X3) ),
    inference(spm,[status(thm)],[c_0_55,c_0_38])).

fof(c_0_61,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r1_tarski(k10_relat_1(esk3_0,esk5_0),esk4_0)
    & k10_relat_1(esk3_0,esk5_0) != k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_56])])])).

fof(c_0_62,plain,(
    ! [X70,X71,X72] :
      ( ~ v1_relat_1(X72)
      | ~ v1_funct_1(X72)
      | ~ r1_tarski(X70,k1_relat_1(X72))
      | ~ r1_tarski(k9_relat_1(X72,X70),X71)
      | r1_tarski(X70,k10_relat_1(X72,X71)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

cnf(c_0_63,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k9_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X2),X1)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_38]),c_0_43]),c_0_39])]),c_0_59])).

cnf(c_0_65,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X2),X1),X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_54])).

cnf(c_0_66,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_68,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(k2_xboole_0(X16,X17),X18)
      | r1_tarski(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_69,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_38]),c_0_39])])).

cnf(c_0_70,plain,
    ( k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(esk3_0,X2))) = k10_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_66])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,k10_relat_1(k6_relat_1(X2),X3))
    | ~ r1_tarski(k9_relat_1(k6_relat_1(X2),X1),X3)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_38]),c_0_39]),c_0_43])])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

fof(c_0_74,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | k2_xboole_0(X19,X20) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_75,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1),X2) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(esk3_0,X1)),X2),k10_relat_1(esk3_0,X1)) = k10_relat_1(k7_relat_1(esk3_0,X2),X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_65])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2))
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_59]),c_0_53])])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_53])).

fof(c_0_79,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_80,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk3_0,X1),X2),X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,k10_relat_1(k6_relat_1(X1),k2_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

fof(c_0_83,plain,(
    ! [X52,X53,X54,X55,X56,X57,X58] :
      ( ( r2_hidden(X55,k1_relat_1(X52))
        | ~ r2_hidden(X55,X54)
        | X54 != k10_relat_1(X52,X53)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( r2_hidden(k1_funct_1(X52,X55),X53)
        | ~ r2_hidden(X55,X54)
        | X54 != k10_relat_1(X52,X53)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( ~ r2_hidden(X56,k1_relat_1(X52))
        | ~ r2_hidden(k1_funct_1(X52,X56),X53)
        | r2_hidden(X56,X54)
        | X54 != k10_relat_1(X52,X53)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( ~ r2_hidden(esk2_3(X52,X57,X58),X58)
        | ~ r2_hidden(esk2_3(X52,X57,X58),k1_relat_1(X52))
        | ~ r2_hidden(k1_funct_1(X52,esk2_3(X52,X57,X58)),X57)
        | X58 = k10_relat_1(X52,X57)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( r2_hidden(esk2_3(X52,X57,X58),k1_relat_1(X52))
        | r2_hidden(esk2_3(X52,X57,X58),X58)
        | X58 = k10_relat_1(X52,X57)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( r2_hidden(k1_funct_1(X52,esk2_3(X52,X57,X58)),X57)
        | r2_hidden(esk2_3(X52,X57,X58),X58)
        | X58 = k10_relat_1(X52,X57)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).

cnf(c_0_84,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_85,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_87,negated_conjecture,
    ( k2_xboole_0(k10_relat_1(k7_relat_1(esk3_0,X1),X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_88,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(X1),k2_xboole_0(X1,X2))),k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(X1),k2_xboole_0(X1,X2))),X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_52,c_0_82])).

cnf(c_0_89,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X3 != k10_relat_1(X2,X4)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_90,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,esk5_0),k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk3_0,X1),X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_73,c_0_87])).

cnf(c_0_93,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(X1),X1),k2_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_88]),c_0_60])).

cnf(c_0_94,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_80,c_0_53])).

cnf(c_0_95,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3)) ),
    inference(er,[status(thm)],[c_0_89])).

cnf(c_0_96,negated_conjecture,
    ( k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0) = k10_relat_1(esk3_0,esk5_0)
    | r2_hidden(esk1_2(k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0),k10_relat_1(esk3_0,esk5_0)),k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( k10_relat_1(esk3_0,esk5_0) != k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(k10_relat_1(k7_relat_1(esk3_0,k10_relat_1(esk3_0,esk5_0)),X1),k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_91])).

cnf(c_0_99,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(X1),X1),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_100,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k10_relat_1(k6_relat_1(X2),X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_38]),c_0_43]),c_0_39])])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(esk1_2(k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0),k10_relat_1(esk3_0,esk5_0)),k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_96]),c_0_59]),c_0_76]),c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk3_0,k10_relat_1(esk3_0,esk5_0)),X1) = k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0)
    | ~ r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0),k10_relat_1(k7_relat_1(esk3_0,k10_relat_1(esk3_0,esk5_0)),X1)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( k10_relat_1(k7_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1) = k10_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_76])).

cnf(c_0_104,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_105,negated_conjecture,
    ( r2_hidden(esk1_2(k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0),k10_relat_1(esk3_0,esk5_0)),k10_relat_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_106,negated_conjecture,
    ( k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0) = k10_relat_1(esk3_0,esk5_0)
    | ~ r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0),k10_relat_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0),k10_relat_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_108,negated_conjecture,
    ( k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0) = k10_relat_1(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_107])])).

cnf(c_0_109,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_108]),c_0_59]),c_0_76]),c_0_97]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:54:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 7.58/7.78  # AutoSched0-Mode selected heuristic G_E___208_C12_02_nc_F1_SE_CS_SP_PS_S002A
% 7.58/7.78  # and selection function SelectNegativeLiterals.
% 7.58/7.78  #
% 7.58/7.78  # Preprocessing time       : 0.028 s
% 7.58/7.78  # Presaturation interreduction done
% 7.58/7.78  
% 7.58/7.78  # Proof found!
% 7.58/7.78  # SZS status Theorem
% 7.58/7.78  # SZS output start CNFRefutation
% 7.58/7.78  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 7.58/7.78  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 7.58/7.78  fof(t147_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 7.58/7.78  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 7.58/7.78  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.58/7.78  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.58/7.78  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 7.58/7.78  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 7.58/7.78  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 7.58/7.78  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 7.58/7.78  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 7.58/7.78  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 7.58/7.78  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 7.58/7.78  fof(t148_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 7.58/7.78  fof(t175_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 7.58/7.78  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 7.58/7.78  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 7.58/7.78  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 7.58/7.78  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.58/7.78  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.58/7.78  fof(d13_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,k1_relat_1(X1))&r2_hidden(k1_funct_1(X1,X4),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_funct_1)).
% 7.58/7.78  fof(c_0_21, plain, ![X48, X49]:k1_setfam_1(k2_tarski(X48,X49))=k3_xboole_0(X48,X49), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 7.58/7.78  fof(c_0_22, plain, ![X21, X22]:k1_enumset1(X21,X21,X22)=k2_tarski(X21,X22), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 7.58/7.78  fof(c_0_23, plain, ![X66, X67]:(~v1_relat_1(X67)|~v1_funct_1(X67)|(~r1_tarski(X66,k2_relat_1(X67))|k9_relat_1(X67,k10_relat_1(X67,X66))=X66)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).
% 7.58/7.78  fof(c_0_24, plain, ![X60]:(v1_relat_1(k6_relat_1(X60))&v1_funct_1(k6_relat_1(X60))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 7.58/7.78  fof(c_0_25, plain, ![X51]:(k1_relat_1(k6_relat_1(X51))=X51&k2_relat_1(k6_relat_1(X51))=X51), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 7.58/7.78  fof(c_0_26, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 7.58/7.78  fof(c_0_27, plain, ![X50]:(~v1_relat_1(X50)|k10_relat_1(X50,k2_relat_1(X50))=k1_relat_1(X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 7.58/7.78  fof(c_0_28, plain, ![X61, X62, X63]:(~v1_relat_1(X63)|k10_relat_1(k7_relat_1(X63,X61),X62)=k3_xboole_0(X61,k10_relat_1(X63,X62))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 7.58/7.78  cnf(c_0_29, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 7.58/7.78  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 7.58/7.78  fof(c_0_31, plain, ![X23, X24, X25]:k2_enumset1(X23,X23,X24,X25)=k1_enumset1(X23,X24,X25), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 7.58/7.78  fof(c_0_32, plain, ![X26, X27, X28, X29]:k3_enumset1(X26,X26,X27,X28,X29)=k2_enumset1(X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 7.58/7.78  fof(c_0_33, plain, ![X30, X31, X32, X33, X34]:k4_enumset1(X30,X30,X31,X32,X33,X34)=k3_enumset1(X30,X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 7.58/7.78  fof(c_0_34, plain, ![X35, X36, X37, X38, X39, X40]:k5_enumset1(X35,X35,X36,X37,X38,X39,X40)=k4_enumset1(X35,X36,X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 7.58/7.78  fof(c_0_35, plain, ![X41, X42, X43, X44, X45, X46, X47]:k6_enumset1(X41,X41,X42,X43,X44,X45,X46,X47)=k5_enumset1(X41,X42,X43,X44,X45,X46,X47), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 7.58/7.78  fof(c_0_36, plain, ![X68, X69]:(~v1_relat_1(X69)|~v1_funct_1(X69)|k9_relat_1(X69,k10_relat_1(X69,X68))=k3_xboole_0(X68,k9_relat_1(X69,k1_relat_1(X69)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).
% 7.58/7.78  cnf(c_0_37, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 7.58/7.78  cnf(c_0_38, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 7.58/7.78  cnf(c_0_39, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 7.58/7.78  cnf(c_0_40, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 7.58/7.78  cnf(c_0_41, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 7.58/7.78  cnf(c_0_42, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 7.58/7.78  cnf(c_0_43, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 7.58/7.78  cnf(c_0_44, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 7.58/7.78  cnf(c_0_45, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 7.58/7.78  cnf(c_0_46, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 7.58/7.78  cnf(c_0_47, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 7.58/7.78  cnf(c_0_48, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 7.58/7.78  cnf(c_0_49, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 7.58/7.78  cnf(c_0_50, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 7.58/7.78  cnf(c_0_51, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 7.58/7.78  cnf(c_0_52, plain, (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2))=X2|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40])])).
% 7.58/7.78  cnf(c_0_53, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_41])).
% 7.58/7.78  cnf(c_0_54, plain, (k10_relat_1(k6_relat_1(X1),X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_38]), c_0_40]), c_0_43])).
% 7.58/7.78  cnf(c_0_55, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 7.58/7.78  fof(c_0_56, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3)))), inference(assume_negation,[status(cth)],[t175_funct_2])).
% 7.58/7.78  fof(c_0_57, plain, ![X64, X65]:(~v1_relat_1(X65)|~v1_funct_1(X65)|r1_tarski(k9_relat_1(X65,k10_relat_1(X65,X64)),X64)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 7.58/7.78  cnf(c_0_58, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k9_relat_1(X1,k1_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 7.58/7.78  cnf(c_0_59, plain, (k9_relat_1(k6_relat_1(X1),X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 7.58/7.78  cnf(c_0_60, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(k6_relat_1(X2),X3)))=k10_relat_1(k7_relat_1(k6_relat_1(X2),X1),X3)), inference(spm,[status(thm)],[c_0_55, c_0_38])).
% 7.58/7.78  fof(c_0_61, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(r1_tarski(k10_relat_1(esk3_0,esk5_0),esk4_0)&k10_relat_1(esk3_0,esk5_0)!=k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_56])])])).
% 7.58/7.78  fof(c_0_62, plain, ![X70, X71, X72]:(~v1_relat_1(X72)|~v1_funct_1(X72)|(~r1_tarski(X70,k1_relat_1(X72))|~r1_tarski(k9_relat_1(X72,X70),X71)|r1_tarski(X70,k10_relat_1(X72,X71)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 7.58/7.78  cnf(c_0_63, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 7.58/7.78  cnf(c_0_64, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k9_relat_1(k6_relat_1(X2),k10_relat_1(k6_relat_1(X2),X1))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_38]), c_0_43]), c_0_39])]), c_0_59])).
% 7.58/7.78  cnf(c_0_65, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k10_relat_1(k7_relat_1(k6_relat_1(X2),X1),X2)), inference(spm,[status(thm)],[c_0_60, c_0_54])).
% 7.58/7.78  cnf(c_0_66, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 7.58/7.78  cnf(c_0_67, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 7.58/7.78  fof(c_0_68, plain, ![X16, X17, X18]:(~r1_tarski(k2_xboole_0(X16,X17),X18)|r1_tarski(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 7.58/7.78  cnf(c_0_69, plain, (r1_tarski(k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_38]), c_0_39])])).
% 7.58/7.78  cnf(c_0_70, plain, (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2))=k10_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 7.58/7.78  cnf(c_0_71, negated_conjecture, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(esk3_0,X2)))=k10_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_55, c_0_66])).
% 7.58/7.78  cnf(c_0_72, plain, (r1_tarski(X1,k10_relat_1(k6_relat_1(X2),X3))|~r1_tarski(k9_relat_1(k6_relat_1(X2),X1),X3)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_38]), c_0_39]), c_0_43])])).
% 7.58/7.78  cnf(c_0_73, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 7.58/7.78  fof(c_0_74, plain, ![X19, X20]:(~r1_tarski(X19,X20)|k2_xboole_0(X19,X20)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 7.58/7.78  cnf(c_0_75, plain, (r1_tarski(k10_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1),X2)), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 7.58/7.78  cnf(c_0_76, negated_conjecture, (k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(esk3_0,X1)),X2),k10_relat_1(esk3_0,X1))=k10_relat_1(k7_relat_1(esk3_0,X2),X1)), inference(spm,[status(thm)],[c_0_71, c_0_65])).
% 7.58/7.78  cnf(c_0_77, plain, (r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2))|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_59]), c_0_53])])).
% 7.58/7.78  cnf(c_0_78, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_73, c_0_53])).
% 7.58/7.78  fof(c_0_79, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 7.58/7.78  cnf(c_0_80, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 7.58/7.78  cnf(c_0_81, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk3_0,X1),X2),X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 7.58/7.78  cnf(c_0_82, plain, (r1_tarski(X1,k10_relat_1(k6_relat_1(X1),k2_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 7.58/7.78  fof(c_0_83, plain, ![X52, X53, X54, X55, X56, X57, X58]:((((r2_hidden(X55,k1_relat_1(X52))|~r2_hidden(X55,X54)|X54!=k10_relat_1(X52,X53)|(~v1_relat_1(X52)|~v1_funct_1(X52)))&(r2_hidden(k1_funct_1(X52,X55),X53)|~r2_hidden(X55,X54)|X54!=k10_relat_1(X52,X53)|(~v1_relat_1(X52)|~v1_funct_1(X52))))&(~r2_hidden(X56,k1_relat_1(X52))|~r2_hidden(k1_funct_1(X52,X56),X53)|r2_hidden(X56,X54)|X54!=k10_relat_1(X52,X53)|(~v1_relat_1(X52)|~v1_funct_1(X52))))&((~r2_hidden(esk2_3(X52,X57,X58),X58)|(~r2_hidden(esk2_3(X52,X57,X58),k1_relat_1(X52))|~r2_hidden(k1_funct_1(X52,esk2_3(X52,X57,X58)),X57))|X58=k10_relat_1(X52,X57)|(~v1_relat_1(X52)|~v1_funct_1(X52)))&((r2_hidden(esk2_3(X52,X57,X58),k1_relat_1(X52))|r2_hidden(esk2_3(X52,X57,X58),X58)|X58=k10_relat_1(X52,X57)|(~v1_relat_1(X52)|~v1_funct_1(X52)))&(r2_hidden(k1_funct_1(X52,esk2_3(X52,X57,X58)),X57)|r2_hidden(esk2_3(X52,X57,X58),X58)|X58=k10_relat_1(X52,X57)|(~v1_relat_1(X52)|~v1_funct_1(X52)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).
% 7.58/7.78  cnf(c_0_84, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 7.58/7.78  cnf(c_0_85, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 7.58/7.78  cnf(c_0_86, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 7.58/7.78  cnf(c_0_87, negated_conjecture, (k2_xboole_0(k10_relat_1(k7_relat_1(esk3_0,X1),X2),X1)=X1), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 7.58/7.78  cnf(c_0_88, plain, (k9_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(X1),k2_xboole_0(X1,X2))),k10_relat_1(k6_relat_1(k10_relat_1(k6_relat_1(X1),k2_xboole_0(X1,X2))),X1))=X1), inference(spm,[status(thm)],[c_0_52, c_0_82])).
% 7.58/7.78  cnf(c_0_89, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,X3)|X3!=k10_relat_1(X2,X4)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 7.58/7.78  cnf(c_0_90, plain, (X1=X2|r2_hidden(esk1_2(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 7.58/7.78  cnf(c_0_91, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,esk5_0),k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0))), inference(spm,[status(thm)],[c_0_77, c_0_86])).
% 7.58/7.78  cnf(c_0_92, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk3_0,X1),X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_73, c_0_87])).
% 7.58/7.78  cnf(c_0_93, plain, (k10_relat_1(k7_relat_1(k6_relat_1(X1),X1),k2_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_88]), c_0_60])).
% 7.58/7.78  cnf(c_0_94, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_80, c_0_53])).
% 7.58/7.78  cnf(c_0_95, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k10_relat_1(X2,X3))), inference(er,[status(thm)],[c_0_89])).
% 7.58/7.78  cnf(c_0_96, negated_conjecture, (k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0)=k10_relat_1(esk3_0,esk5_0)|r2_hidden(esk1_2(k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0),k10_relat_1(esk3_0,esk5_0)),k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 7.58/7.78  cnf(c_0_97, negated_conjecture, (k10_relat_1(esk3_0,esk5_0)!=k10_relat_1(k7_relat_1(esk3_0,esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 7.58/7.78  cnf(c_0_98, negated_conjecture, (r1_tarski(k10_relat_1(k7_relat_1(esk3_0,k10_relat_1(esk3_0,esk5_0)),X1),k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0))), inference(spm,[status(thm)],[c_0_92, c_0_91])).
% 7.58/7.78  cnf(c_0_99, plain, (k10_relat_1(k7_relat_1(k6_relat_1(X1),X1),X1)=X1), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 7.58/7.78  cnf(c_0_100, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k10_relat_1(k6_relat_1(X2),X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_38]), c_0_43]), c_0_39])])).
% 7.58/7.78  cnf(c_0_101, negated_conjecture, (r2_hidden(esk1_2(k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0),k10_relat_1(esk3_0,esk5_0)),k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_96]), c_0_59]), c_0_76]), c_0_97])).
% 7.58/7.78  cnf(c_0_102, negated_conjecture, (k10_relat_1(k7_relat_1(esk3_0,k10_relat_1(esk3_0,esk5_0)),X1)=k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0)|~r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0),k10_relat_1(k7_relat_1(esk3_0,k10_relat_1(esk3_0,esk5_0)),X1))), inference(spm,[status(thm)],[c_0_84, c_0_98])).
% 7.58/7.78  cnf(c_0_103, negated_conjecture, (k10_relat_1(k7_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1)=k10_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_99, c_0_76])).
% 7.58/7.78  cnf(c_0_104, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 7.58/7.78  cnf(c_0_105, negated_conjecture, (r2_hidden(esk1_2(k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0),k10_relat_1(esk3_0,esk5_0)),k10_relat_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 7.58/7.78  cnf(c_0_106, negated_conjecture, (k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0)=k10_relat_1(esk3_0,esk5_0)|~r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0),k10_relat_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 7.58/7.78  cnf(c_0_107, negated_conjecture, (r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0),k10_relat_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 7.58/7.78  cnf(c_0_108, negated_conjecture, (k10_relat_1(k6_relat_1(k10_relat_1(esk3_0,esk5_0)),esk4_0)=k10_relat_1(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_107])])).
% 7.58/7.78  cnf(c_0_109, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_108]), c_0_59]), c_0_76]), c_0_97]), ['proof']).
% 7.58/7.78  # SZS output end CNFRefutation
% 7.58/7.78  # Proof object total steps             : 110
% 7.58/7.78  # Proof object clause steps            : 67
% 7.58/7.78  # Proof object formula steps           : 43
% 7.58/7.78  # Proof object conjectures             : 22
% 7.58/7.78  # Proof object clause conjectures      : 19
% 7.58/7.78  # Proof object formula conjectures     : 3
% 7.58/7.78  # Proof object initial clauses used    : 27
% 7.58/7.78  # Proof object initial formulas used   : 21
% 7.58/7.78  # Proof object generating inferences   : 33
% 7.58/7.78  # Proof object simplifying inferences  : 45
% 7.58/7.78  # Training examples: 0 positive, 0 negative
% 7.58/7.78  # Parsed axioms                        : 21
% 7.58/7.78  # Removed by relevancy pruning/SinE    : 0
% 7.58/7.78  # Initial clauses                      : 35
% 7.58/7.78  # Removed in clause preprocessing      : 7
% 7.58/7.78  # Initial clauses in saturation        : 28
% 7.58/7.78  # Processed clauses                    : 10047
% 7.58/7.78  # ...of these trivial                  : 277
% 7.58/7.78  # ...subsumed                          : 6222
% 7.58/7.78  # ...remaining for further processing  : 3548
% 7.58/7.78  # Other redundant clauses eliminated   : 6361
% 7.58/7.78  # Clauses deleted for lack of memory   : 0
% 7.58/7.78  # Backward-subsumed                    : 489
% 7.58/7.78  # Backward-rewritten                   : 927
% 7.58/7.78  # Generated clauses                    : 868541
% 7.58/7.78  # ...of the previous two non-trivial   : 793816
% 7.58/7.78  # Contextual simplify-reflections      : 155
% 7.58/7.78  # Paramodulations                      : 862103
% 7.58/7.78  # Factorizations                       : 30
% 7.58/7.78  # Equation resolutions                 : 6408
% 7.58/7.78  # Propositional unsat checks           : 0
% 7.58/7.78  #    Propositional check models        : 0
% 7.58/7.78  #    Propositional check unsatisfiable : 0
% 7.58/7.78  #    Propositional clauses             : 0
% 7.58/7.78  #    Propositional clauses after purity: 0
% 7.58/7.78  #    Propositional unsat core size     : 0
% 7.58/7.78  #    Propositional preprocessing time  : 0.000
% 7.58/7.78  #    Propositional encoding time       : 0.000
% 7.58/7.78  #    Propositional solver time         : 0.000
% 7.58/7.78  #    Success case prop preproc time    : 0.000
% 7.58/7.78  #    Success case prop encoding time   : 0.000
% 7.58/7.78  #    Success case prop solver time     : 0.000
% 7.58/7.78  # Current number of processed clauses  : 2100
% 7.58/7.78  #    Positive orientable unit clauses  : 249
% 7.58/7.78  #    Positive unorientable unit clauses: 1
% 7.58/7.78  #    Negative unit clauses             : 1
% 7.58/7.78  #    Non-unit-clauses                  : 1849
% 7.58/7.78  # Current number of unprocessed clauses: 782108
% 7.58/7.78  # ...number of literals in the above   : 3647961
% 7.58/7.78  # Current number of archived formulas  : 0
% 7.58/7.78  # Current number of archived clauses   : 1450
% 7.58/7.78  # Clause-clause subsumption calls (NU) : 1049494
% 7.58/7.78  # Rec. Clause-clause subsumption calls : 446185
% 7.58/7.78  # Non-unit clause-clause subsumptions  : 6848
% 7.58/7.78  # Unit Clause-clause subsumption calls : 58953
% 7.58/7.78  # Rewrite failures with RHS unbound    : 0
% 7.58/7.78  # BW rewrite match attempts            : 2298
% 7.58/7.78  # BW rewrite match successes           : 120
% 7.58/7.78  # Condensation attempts                : 0
% 7.58/7.78  # Condensation successes               : 0
% 7.58/7.78  # Termbank termtop insertions          : 24295876
% 7.61/7.80  
% 7.61/7.80  # -------------------------------------------------
% 7.61/7.80  # User time                : 7.108 s
% 7.61/7.80  # System time              : 0.349 s
% 7.61/7.80  # Total time               : 7.456 s
% 7.61/7.80  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
