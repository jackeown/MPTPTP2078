%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:48 EST 2020

% Result     : Theorem 0.86s
% Output     : CNFRefutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :  115 (1503 expanded)
%              Number of clauses        :   64 ( 621 expanded)
%              Number of leaves         :   25 ( 439 expanded)
%              Depth                    :   13
%              Number of atoms          :  231 (2262 expanded)
%              Number of equality atoms :   84 (1327 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t43_funct_1,axiom,(
    ! [X1,X2] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

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

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t160_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(t29_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k2_wellord1(k2_wellord1(X3,X2),X1) = k2_wellord1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

fof(t26_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k2_wellord1(k2_wellord1(X3,X1),X2) = k2_wellord1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(t18_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,X1) = k8_relat_1(X1,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

fof(c_0_25,plain,(
    ! [X42,X43] : k1_setfam_1(k2_tarski(X42,X43)) = k3_xboole_0(X42,X43) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_26,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,plain,(
    ! [X46,X47] :
      ( ~ v1_relat_1(X46)
      | ~ m1_subset_1(X47,k1_zfmisc_1(X46))
      | v1_relat_1(X47) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_28,plain,(
    ! [X44,X45] :
      ( ( ~ m1_subset_1(X44,k1_zfmisc_1(X45))
        | r1_tarski(X44,X45) )
      & ( ~ r1_tarski(X44,X45)
        | m1_subset_1(X44,k1_zfmisc_1(X45)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_29,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_30,plain,(
    ! [X64,X65] : k5_relat_1(k6_relat_1(X65),k6_relat_1(X64)) = k6_relat_1(k3_xboole_0(X64,X65)) ),
    inference(variable_rename,[status(thm)],[t43_funct_1])).

cnf(c_0_31,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_34,plain,(
    ! [X20,X21,X22,X23] : k3_enumset1(X20,X20,X21,X22,X23) = k2_enumset1(X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_35,plain,(
    ! [X24,X25,X26,X27,X28] : k4_enumset1(X24,X24,X25,X26,X27,X28) = k3_enumset1(X24,X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_36,plain,(
    ! [X29,X30,X31,X32,X33,X34] : k5_enumset1(X29,X29,X30,X31,X32,X33,X34) = k4_enumset1(X29,X30,X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_37,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41] : k6_enumset1(X35,X35,X36,X37,X38,X39,X40,X41) = k5_enumset1(X35,X36,X37,X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_38,plain,(
    ! [X56,X57] :
      ( ( r1_tarski(k1_relat_1(X56),k1_relat_1(X57))
        | ~ r1_tarski(X56,X57)
        | ~ v1_relat_1(X57)
        | ~ v1_relat_1(X56) )
      & ( r1_tarski(k2_relat_1(X56),k2_relat_1(X57))
        | ~ r1_tarski(X56,X57)
        | ~ v1_relat_1(X57)
        | ~ v1_relat_1(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_39,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_41,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | ~ r1_tarski(X11,X12)
      | r1_tarski(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_42,plain,(
    ! [X59,X60] :
      ( ~ v1_relat_1(X60)
      | r1_tarski(k7_relat_1(X60,X59),X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

fof(c_0_43,plain,(
    ! [X61,X62] :
      ( ~ v1_relat_1(X62)
      | ~ r1_tarski(k1_relat_1(X62),X61)
      | k7_relat_1(X62,X61) = X62 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_45,plain,(
    ! [X58] :
      ( k1_relat_1(k6_relat_1(X58)) = X58
      & k2_relat_1(k6_relat_1(X58)) = X58 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_46,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_47,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_48,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_51,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_52,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_53,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_54,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_56,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_57,plain,(
    ! [X48,X49] :
      ( ~ v1_relat_1(X48)
      | v1_relat_1(k7_relat_1(X48,X49)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_58,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_44])).

fof(c_0_60,plain,(
    ! [X63] :
      ( v1_relat_1(k6_relat_1(X63))
      & v1_funct_1(k6_relat_1(X63)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_61,plain,(
    ! [X13,X14] : k2_tarski(X13,X14) = k2_tarski(X14,X13) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_62,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_63,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52])).

fof(c_0_64,plain,(
    ! [X52,X53] :
      ( ~ v1_relat_1(X53)
      | k2_relat_1(k7_relat_1(X53,X52)) = k9_relat_1(X53,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_65,plain,(
    ! [X54,X55] :
      ( ~ v1_relat_1(X54)
      | ~ v1_relat_1(X55)
      | k2_relat_1(k5_relat_1(X54,X55)) = k9_relat_1(X55,k2_relat_1(X54)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).

cnf(c_0_66,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k7_relat_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_68,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_69,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_70,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_71,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_72,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => k2_wellord1(k2_wellord1(X3,X2),X1) = k2_wellord1(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t29_wellord1])).

cnf(c_0_73,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_74,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_75,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_76,plain,
    ( k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_relat_1(X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_66])).

cnf(c_0_78,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(X1,X2),X3),X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_56]),c_0_68])).

cnf(c_0_79,plain,
    ( k7_relat_1(k6_relat_1(X1),X1) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])])).

fof(c_0_80,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_tarski(esk1_0,esk2_0)
    & k2_wellord1(k2_wellord1(esk3_0,esk2_0),esk1_0) != k2_wellord1(esk3_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_72])])])).

fof(c_0_81,plain,(
    ! [X68,X69,X70] :
      ( ~ v1_relat_1(X70)
      | k2_wellord1(k2_wellord1(X70,X68),X69) = k2_wellord1(X70,k3_xboole_0(X68,X69)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_wellord1])])).

fof(c_0_82,plain,(
    ! [X50,X51] :
      ( ~ v1_relat_1(X51)
      | ~ r1_tarski(k2_relat_1(X51),X50)
      | k8_relat_1(X50,X51) = X51 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

fof(c_0_83,plain,(
    ! [X66,X67] :
      ( ~ v1_relat_1(X67)
      | k2_wellord1(X67,X66) = k8_relat_1(X66,k7_relat_1(X67,X66)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_wellord1])])).

cnf(c_0_84,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_32]),c_0_32]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52])).

cnf(c_0_85,plain,
    ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_63,c_0_74])).

cnf(c_0_86,plain,
    ( k2_relat_1(k5_relat_1(X1,X2)) = k2_relat_1(k7_relat_1(X2,k2_relat_1(X1)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_87,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_66]),c_0_54])).

cnf(c_0_88,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_71])])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_90,plain,
    ( k2_wellord1(k2_wellord1(X1,X2),X3) = k2_wellord1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_91,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_92,plain,
    ( k2_wellord1(X1,X2) = k8_relat_1(X2,k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_93,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_84]),c_0_74])).

cnf(c_0_94,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_62]),c_0_71]),c_0_71])])).

cnf(c_0_95,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(X1,k7_relat_1(k6_relat_1(X2),X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_62]),c_0_71])])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_89])).

cnf(c_0_97,plain,
    ( k2_wellord1(k2_wellord1(X1,X2),X3) = k2_wellord1(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_98,plain,
    ( k7_relat_1(X1,X2) = k2_wellord1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_68])).

cnf(c_0_99,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94]),c_0_62]),c_0_94]),c_0_62])).

cnf(c_0_100,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_59])).

cnf(c_0_101,negated_conjecture,
    ( k7_relat_1(X1,esk2_0) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_96])).

cnf(c_0_102,plain,
    ( k2_wellord1(X1,k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))) = k2_wellord1(k2_wellord1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_97,c_0_74])).

cnf(c_0_103,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k2_wellord1(k6_relat_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_71]),c_0_100])])).

cnf(c_0_104,negated_conjecture,
    ( k7_relat_1(X1,esk2_0) = k2_wellord1(X1,esk2_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(X1,esk2_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_96])).

cnf(c_0_105,negated_conjecture,
    ( k7_relat_1(k6_relat_1(X1),esk2_0) = k6_relat_1(X1)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_70]),c_0_71])])).

cnf(c_0_106,plain,
    ( k2_wellord1(X1,k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k2_wellord1(k2_wellord1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_94]),c_0_62])).

cnf(c_0_107,plain,
    ( k2_relat_1(k2_wellord1(k6_relat_1(X1),X2)) = k2_relat_1(k2_wellord1(k6_relat_1(X2),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_103]),c_0_103])).

cnf(c_0_108,negated_conjecture,
    ( k2_wellord1(k6_relat_1(X1),esk2_0) = k6_relat_1(X1)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_71]),c_0_62])])).

cnf(c_0_109,plain,
    ( k2_wellord1(X1,k2_relat_1(k2_wellord1(k6_relat_1(X2),X3))) = k2_wellord1(k2_wellord1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_106,c_0_103])).

cnf(c_0_110,negated_conjecture,
    ( k2_relat_1(k2_wellord1(k6_relat_1(esk2_0),X1)) = X1
    | ~ r1_tarski(X1,esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_62])).

cnf(c_0_111,negated_conjecture,
    ( k2_wellord1(k2_wellord1(esk3_0,esk2_0),esk1_0) != k2_wellord1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_112,negated_conjecture,
    ( k2_wellord1(k2_wellord1(X1,esk2_0),X2) = k2_wellord1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,esk1_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_113,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_114,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_113]),c_0_59])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.86/1.07  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.86/1.07  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.86/1.07  #
% 0.86/1.07  # Preprocessing time       : 0.028 s
% 0.86/1.07  # Presaturation interreduction done
% 0.86/1.07  
% 0.86/1.07  # Proof found!
% 0.86/1.07  # SZS status Theorem
% 0.86/1.07  # SZS output start CNFRefutation
% 0.86/1.07  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.86/1.07  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.86/1.07  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.86/1.07  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.86/1.07  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.86/1.07  fof(t43_funct_1, axiom, ![X1, X2]:k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))=k6_relat_1(k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 0.86/1.07  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.86/1.07  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.86/1.07  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.86/1.07  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.86/1.07  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.86/1.07  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 0.86/1.07  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.86/1.07  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 0.86/1.07  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 0.86/1.07  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.86/1.07  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.86/1.07  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.86/1.07  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.86/1.07  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.86/1.07  fof(t160_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 0.86/1.07  fof(t29_wellord1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k2_wellord1(k2_wellord1(X3,X2),X1)=k2_wellord1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_wellord1)).
% 0.86/1.07  fof(t26_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k2_wellord1(k2_wellord1(X3,X1),X2)=k2_wellord1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_wellord1)).
% 0.86/1.07  fof(t125_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k8_relat_1(X1,X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 0.86/1.07  fof(t18_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_wellord1(X2,X1)=k8_relat_1(X1,k7_relat_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_wellord1)).
% 0.86/1.07  fof(c_0_25, plain, ![X42, X43]:k1_setfam_1(k2_tarski(X42,X43))=k3_xboole_0(X42,X43), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.86/1.07  fof(c_0_26, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.86/1.07  fof(c_0_27, plain, ![X46, X47]:(~v1_relat_1(X46)|(~m1_subset_1(X47,k1_zfmisc_1(X46))|v1_relat_1(X47))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.86/1.07  fof(c_0_28, plain, ![X44, X45]:((~m1_subset_1(X44,k1_zfmisc_1(X45))|r1_tarski(X44,X45))&(~r1_tarski(X44,X45)|m1_subset_1(X44,k1_zfmisc_1(X45)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.86/1.07  fof(c_0_29, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.86/1.07  fof(c_0_30, plain, ![X64, X65]:k5_relat_1(k6_relat_1(X65),k6_relat_1(X64))=k6_relat_1(k3_xboole_0(X64,X65)), inference(variable_rename,[status(thm)],[t43_funct_1])).
% 0.86/1.07  cnf(c_0_31, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.86/1.07  cnf(c_0_32, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.86/1.07  fof(c_0_33, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.86/1.07  fof(c_0_34, plain, ![X20, X21, X22, X23]:k3_enumset1(X20,X20,X21,X22,X23)=k2_enumset1(X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.86/1.07  fof(c_0_35, plain, ![X24, X25, X26, X27, X28]:k4_enumset1(X24,X24,X25,X26,X27,X28)=k3_enumset1(X24,X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.86/1.07  fof(c_0_36, plain, ![X29, X30, X31, X32, X33, X34]:k5_enumset1(X29,X29,X30,X31,X32,X33,X34)=k4_enumset1(X29,X30,X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.86/1.07  fof(c_0_37, plain, ![X35, X36, X37, X38, X39, X40, X41]:k6_enumset1(X35,X35,X36,X37,X38,X39,X40,X41)=k5_enumset1(X35,X36,X37,X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.86/1.07  fof(c_0_38, plain, ![X56, X57]:((r1_tarski(k1_relat_1(X56),k1_relat_1(X57))|~r1_tarski(X56,X57)|~v1_relat_1(X57)|~v1_relat_1(X56))&(r1_tarski(k2_relat_1(X56),k2_relat_1(X57))|~r1_tarski(X56,X57)|~v1_relat_1(X57)|~v1_relat_1(X56))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.86/1.07  cnf(c_0_39, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.86/1.07  cnf(c_0_40, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.86/1.07  fof(c_0_41, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|~r1_tarski(X11,X12)|r1_tarski(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.86/1.07  fof(c_0_42, plain, ![X59, X60]:(~v1_relat_1(X60)|r1_tarski(k7_relat_1(X60,X59),X60)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.86/1.07  fof(c_0_43, plain, ![X61, X62]:(~v1_relat_1(X62)|(~r1_tarski(k1_relat_1(X62),X61)|k7_relat_1(X62,X61)=X62)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.86/1.07  cnf(c_0_44, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.86/1.07  fof(c_0_45, plain, ![X58]:(k1_relat_1(k6_relat_1(X58))=X58&k2_relat_1(k6_relat_1(X58))=X58), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.86/1.07  cnf(c_0_46, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k3_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.86/1.07  cnf(c_0_47, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.86/1.07  cnf(c_0_48, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.86/1.07  cnf(c_0_49, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.86/1.07  cnf(c_0_50, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.86/1.07  cnf(c_0_51, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.86/1.07  cnf(c_0_52, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.86/1.07  cnf(c_0_53, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.86/1.07  cnf(c_0_54, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.86/1.07  cnf(c_0_55, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.86/1.07  cnf(c_0_56, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.86/1.07  fof(c_0_57, plain, ![X48, X49]:(~v1_relat_1(X48)|v1_relat_1(k7_relat_1(X48,X49))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.86/1.07  cnf(c_0_58, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.86/1.07  cnf(c_0_59, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_44])).
% 0.86/1.07  fof(c_0_60, plain, ![X63]:(v1_relat_1(k6_relat_1(X63))&v1_funct_1(k6_relat_1(X63))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.86/1.07  fof(c_0_61, plain, ![X13, X14]:k2_tarski(X13,X14)=k2_tarski(X14,X13), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.86/1.07  cnf(c_0_62, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.86/1.07  cnf(c_0_63, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_52])).
% 0.86/1.07  fof(c_0_64, plain, ![X52, X53]:(~v1_relat_1(X53)|k2_relat_1(k7_relat_1(X53,X52))=k9_relat_1(X53,X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.86/1.07  fof(c_0_65, plain, ![X54, X55]:(~v1_relat_1(X54)|(~v1_relat_1(X55)|k2_relat_1(k5_relat_1(X54,X55))=k9_relat_1(X55,k2_relat_1(X54)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).
% 0.86/1.07  cnf(c_0_66, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[c_0_53, c_0_54])).
% 0.86/1.07  cnf(c_0_67, plain, (r1_tarski(X1,X2)|~v1_relat_1(X2)|~r1_tarski(X1,k7_relat_1(X2,X3))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.86/1.07  cnf(c_0_68, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.86/1.07  cnf(c_0_69, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.86/1.07  cnf(c_0_70, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.86/1.07  cnf(c_0_71, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.86/1.07  fof(c_0_72, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k2_wellord1(k2_wellord1(X3,X2),X1)=k2_wellord1(X3,X1)))), inference(assume_negation,[status(cth)],[t29_wellord1])).
% 0.86/1.07  cnf(c_0_73, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.86/1.07  cnf(c_0_74, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.86/1.07  cnf(c_0_75, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.86/1.07  cnf(c_0_76, plain, (k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.86/1.07  cnf(c_0_77, plain, (r1_tarski(X1,k2_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k2_relat_1(X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_55, c_0_66])).
% 0.86/1.07  cnf(c_0_78, plain, (r1_tarski(k7_relat_1(k7_relat_1(X1,X2),X3),X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_56]), c_0_68])).
% 0.86/1.07  cnf(c_0_79, plain, (k7_relat_1(k6_relat_1(X1),X1)=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])])).
% 0.86/1.07  fof(c_0_80, negated_conjecture, (v1_relat_1(esk3_0)&(r1_tarski(esk1_0,esk2_0)&k2_wellord1(k2_wellord1(esk3_0,esk2_0),esk1_0)!=k2_wellord1(esk3_0,esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_72])])])).
% 0.86/1.07  fof(c_0_81, plain, ![X68, X69, X70]:(~v1_relat_1(X70)|k2_wellord1(k2_wellord1(X70,X68),X69)=k2_wellord1(X70,k3_xboole_0(X68,X69))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_wellord1])])).
% 0.86/1.07  fof(c_0_82, plain, ![X50, X51]:(~v1_relat_1(X51)|(~r1_tarski(k2_relat_1(X51),X50)|k8_relat_1(X50,X51)=X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).
% 0.86/1.07  fof(c_0_83, plain, ![X66, X67]:(~v1_relat_1(X67)|k2_wellord1(X67,X66)=k8_relat_1(X66,k7_relat_1(X67,X66))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_wellord1])])).
% 0.86/1.07  cnf(c_0_84, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_32]), c_0_32]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_52]), c_0_52])).
% 0.86/1.07  cnf(c_0_85, plain, (k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))=k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_63, c_0_74])).
% 0.86/1.07  cnf(c_0_86, plain, (k2_relat_1(k5_relat_1(X1,X2))=k2_relat_1(k7_relat_1(X2,k2_relat_1(X1)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.86/1.07  cnf(c_0_87, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_66]), c_0_54])).
% 0.86/1.07  cnf(c_0_88, plain, (r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_71])])).
% 0.86/1.07  cnf(c_0_89, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.86/1.07  cnf(c_0_90, plain, (k2_wellord1(k2_wellord1(X1,X2),X3)=k2_wellord1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.86/1.07  cnf(c_0_91, plain, (k8_relat_1(X2,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.86/1.07  cnf(c_0_92, plain, (k2_wellord1(X1,X2)=k8_relat_1(X2,k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.86/1.07  cnf(c_0_93, plain, (k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))=k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_84]), c_0_74])).
% 0.86/1.07  cnf(c_0_94, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_62]), c_0_71]), c_0_71])])).
% 0.86/1.07  cnf(c_0_95, plain, (r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(X1,k7_relat_1(k6_relat_1(X2),X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_62]), c_0_71])])).
% 0.86/1.07  cnf(c_0_96, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_55, c_0_89])).
% 0.86/1.07  cnf(c_0_97, plain, (k2_wellord1(k2_wellord1(X1,X2),X3)=k2_wellord1(X1,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_47]), c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_52])).
% 0.86/1.07  cnf(c_0_98, plain, (k7_relat_1(X1,X2)=k2_wellord1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_68])).
% 0.86/1.07  cnf(c_0_99, plain, (k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k2_relat_1(k7_relat_1(k6_relat_1(X2),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_94]), c_0_62]), c_0_94]), c_0_62])).
% 0.86/1.07  cnf(c_0_100, plain, (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1)), inference(spm,[status(thm)],[c_0_95, c_0_59])).
% 0.86/1.07  cnf(c_0_101, negated_conjecture, (k7_relat_1(X1,esk2_0)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),esk1_0)), inference(spm,[status(thm)],[c_0_58, c_0_96])).
% 0.86/1.07  cnf(c_0_102, plain, (k2_wellord1(X1,k2_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))))=k2_wellord1(k2_wellord1(X1,X3),X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_97, c_0_74])).
% 0.86/1.07  cnf(c_0_103, plain, (k7_relat_1(k6_relat_1(X1),X2)=k2_wellord1(k6_relat_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_71]), c_0_100])])).
% 0.86/1.07  cnf(c_0_104, negated_conjecture, (k7_relat_1(X1,esk2_0)=k2_wellord1(X1,esk2_0)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(k7_relat_1(X1,esk2_0)),esk1_0)), inference(spm,[status(thm)],[c_0_98, c_0_96])).
% 0.86/1.07  cnf(c_0_105, negated_conjecture, (k7_relat_1(k6_relat_1(X1),esk2_0)=k6_relat_1(X1)|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_70]), c_0_71])])).
% 0.86/1.07  cnf(c_0_106, plain, (k2_wellord1(X1,k2_relat_1(k7_relat_1(k6_relat_1(X2),X3)))=k2_wellord1(k2_wellord1(X1,X2),X3)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_94]), c_0_62])).
% 0.86/1.07  cnf(c_0_107, plain, (k2_relat_1(k2_wellord1(k6_relat_1(X1),X2))=k2_relat_1(k2_wellord1(k6_relat_1(X2),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_103]), c_0_103])).
% 0.86/1.07  cnf(c_0_108, negated_conjecture, (k2_wellord1(k6_relat_1(X1),esk2_0)=k6_relat_1(X1)|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_71]), c_0_62])])).
% 0.86/1.07  cnf(c_0_109, plain, (k2_wellord1(X1,k2_relat_1(k2_wellord1(k6_relat_1(X2),X3)))=k2_wellord1(k2_wellord1(X1,X2),X3)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_106, c_0_103])).
% 0.86/1.07  cnf(c_0_110, negated_conjecture, (k2_relat_1(k2_wellord1(k6_relat_1(esk2_0),X1))=X1|~r1_tarski(X1,esk1_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_62])).
% 0.86/1.07  cnf(c_0_111, negated_conjecture, (k2_wellord1(k2_wellord1(esk3_0,esk2_0),esk1_0)!=k2_wellord1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.86/1.07  cnf(c_0_112, negated_conjecture, (k2_wellord1(k2_wellord1(X1,esk2_0),X2)=k2_wellord1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,esk1_0)), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 0.86/1.07  cnf(c_0_113, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.86/1.07  cnf(c_0_114, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_113]), c_0_59])]), ['proof']).
% 0.86/1.07  # SZS output end CNFRefutation
% 0.86/1.07  # Proof object total steps             : 115
% 0.86/1.07  # Proof object clause steps            : 64
% 0.86/1.07  # Proof object formula steps           : 51
% 0.86/1.07  # Proof object conjectures             : 14
% 0.86/1.07  # Proof object clause conjectures      : 11
% 0.86/1.07  # Proof object formula conjectures     : 3
% 0.86/1.07  # Proof object initial clauses used    : 28
% 0.86/1.07  # Proof object initial formulas used   : 25
% 0.86/1.07  # Proof object generating inferences   : 24
% 0.86/1.07  # Proof object simplifying inferences  : 65
% 0.86/1.07  # Training examples: 0 positive, 0 negative
% 0.86/1.07  # Parsed axioms                        : 25
% 0.86/1.07  # Removed by relevancy pruning/SinE    : 0
% 0.86/1.07  # Initial clauses                      : 33
% 0.86/1.07  # Removed in clause preprocessing      : 7
% 0.86/1.07  # Initial clauses in saturation        : 26
% 0.86/1.07  # Processed clauses                    : 5655
% 0.86/1.07  # ...of these trivial                  : 68
% 0.86/1.07  # ...subsumed                          : 3992
% 0.86/1.07  # ...remaining for further processing  : 1595
% 0.86/1.07  # Other redundant clauses eliminated   : 2
% 0.86/1.07  # Clauses deleted for lack of memory   : 0
% 0.86/1.07  # Backward-subsumed                    : 81
% 0.86/1.07  # Backward-rewritten                   : 139
% 0.86/1.07  # Generated clauses                    : 40437
% 0.86/1.07  # ...of the previous two non-trivial   : 38724
% 0.86/1.07  # Contextual simplify-reflections      : 186
% 0.86/1.07  # Paramodulations                      : 40435
% 0.86/1.07  # Factorizations                       : 0
% 0.86/1.07  # Equation resolutions                 : 2
% 0.86/1.07  # Propositional unsat checks           : 0
% 0.86/1.07  #    Propositional check models        : 0
% 0.86/1.07  #    Propositional check unsatisfiable : 0
% 0.86/1.07  #    Propositional clauses             : 0
% 0.86/1.07  #    Propositional clauses after purity: 0
% 0.86/1.07  #    Propositional unsat core size     : 0
% 0.86/1.07  #    Propositional preprocessing time  : 0.000
% 0.86/1.07  #    Propositional encoding time       : 0.000
% 0.86/1.07  #    Propositional solver time         : 0.000
% 0.86/1.07  #    Success case prop preproc time    : 0.000
% 0.86/1.07  #    Success case prop encoding time   : 0.000
% 0.86/1.07  #    Success case prop solver time     : 0.000
% 0.86/1.07  # Current number of processed clauses  : 1348
% 0.86/1.07  #    Positive orientable unit clauses  : 62
% 0.86/1.07  #    Positive unorientable unit clauses: 2
% 0.86/1.07  #    Negative unit clauses             : 1
% 0.86/1.07  #    Non-unit-clauses                  : 1283
% 0.86/1.07  # Current number of unprocessed clauses: 32516
% 0.86/1.07  # ...number of literals in the above   : 134501
% 0.86/1.07  # Current number of archived formulas  : 0
% 0.86/1.07  # Current number of archived clauses   : 252
% 0.86/1.07  # Clause-clause subsumption calls (NU) : 375057
% 0.86/1.07  # Rec. Clause-clause subsumption calls : 121146
% 0.86/1.07  # Non-unit clause-clause subsumptions  : 4257
% 0.86/1.07  # Unit Clause-clause subsumption calls : 99
% 0.86/1.07  # Rewrite failures with RHS unbound    : 0
% 0.86/1.07  # BW rewrite match attempts            : 324
% 0.86/1.07  # BW rewrite match successes           : 81
% 0.86/1.07  # Condensation attempts                : 0
% 0.86/1.07  # Condensation successes               : 0
% 0.86/1.07  # Termbank termtop insertions          : 717141
% 0.86/1.08  
% 0.86/1.08  # -------------------------------------------------
% 0.86/1.08  # User time                : 0.710 s
% 0.86/1.08  # System time              : 0.023 s
% 0.86/1.08  # Total time               : 0.732 s
% 0.86/1.08  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
