%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:17 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 106 expanded)
%              Number of clauses        :   37 (  48 expanded)
%              Number of leaves         :   13 (  26 expanded)
%              Depth                    :   12
%              Number of atoms          :  148 ( 273 expanded)
%              Number of equality atoms :   28 (  45 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t158_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))
          & r1_tarski(X1,k2_relat_1(X3)) )
       => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t73_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t173_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t138_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k10_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(c_0_13,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(k2_xboole_0(X7,X8),X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_14,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k2_xboole_0(X10,X11) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X32,X33] : r1_tarski(X32,k2_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))
            & r1_tarski(X1,k2_relat_1(X3)) )
         => r1_tarski(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t158_funct_1])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & r1_tarski(k10_relat_1(esk4_0,esk2_0),k10_relat_1(esk4_0,esk3_0))
    & r1_tarski(esk2_0,k2_relat_1(esk4_0))
    & ~ r1_tarski(esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_23,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(k4_xboole_0(X23,X24),X25)
      | r1_tarski(X23,k2_xboole_0(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,esk2_0),k10_relat_1(esk4_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_27,plain,(
    ! [X29,X30,X31] :
      ( ~ r1_tarski(X29,k2_xboole_0(X30,X31))
      | ~ r1_xboole_0(X29,X31)
      | r1_tarski(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,esk2_0),k2_xboole_0(X1,X2))
    | ~ r1_tarski(k10_relat_1(esk4_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(k4_xboole_0(X1,X2),X3))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_19])).

fof(c_0_33,plain,(
    ! [X26,X27,X28] :
      ( ~ r1_tarski(X26,X27)
      | ~ r1_xboole_0(X27,X28)
      | r1_xboole_0(X26,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_34,plain,(
    ! [X36,X37] :
      ( ( k10_relat_1(X37,X36) != k1_xboole_0
        | r1_xboole_0(k2_relat_1(X37),X36)
        | ~ v1_relat_1(X37) )
      & ( ~ r1_xboole_0(k2_relat_1(X37),X36)
        | k10_relat_1(X37,X36) = k1_xboole_0
        | ~ v1_relat_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t173_relat_1])])])).

fof(c_0_35,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,k4_xboole_0(X19,X18))
      | X18 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

fof(c_0_36,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,k2_xboole_0(X21,X22))
      | r1_tarski(k4_xboole_0(X20,X21),X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,esk2_0),X1)
    | ~ r1_tarski(k10_relat_1(esk4_0,esk3_0),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_16])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( r1_xboole_0(k2_relat_1(X1),X2)
    | k10_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_42,plain,(
    ! [X38,X39,X40] :
      ( ~ v1_relat_1(X40)
      | ~ v1_funct_1(X40)
      | k10_relat_1(X40,k6_subset_1(X38,X39)) = k6_subset_1(k10_relat_1(X40,X38),k10_relat_1(X40,X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).

fof(c_0_43,plain,(
    ! [X34,X35] : k6_subset_1(X34,X35) = k4_xboole_0(X34,X35) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,esk2_0),X1)
    | ~ r1_tarski(k10_relat_1(esk4_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_16])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,X2)
    | k10_relat_1(X3,X2) != k1_xboole_0
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k2_relat_1(X3)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk2_0,k2_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_50,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_51,plain,
    ( k10_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,k2_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,esk2_0),k2_xboole_0(k10_relat_1(esk4_0,esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_19])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_38])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(esk2_0,X1)
    | k10_relat_1(esk4_0,X1) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])])).

cnf(c_0_57,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(k10_relat_1(esk4_0,esk2_0),k10_relat_1(esk4_0,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | k10_relat_1(esk4_0,k4_xboole_0(esk2_0,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( k10_relat_1(esk4_0,k4_xboole_0(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_50])])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n010.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:19:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.47  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.47  #
% 0.20/0.47  # Preprocessing time       : 0.028 s
% 0.20/0.47  # Presaturation interreduction done
% 0.20/0.47  
% 0.20/0.47  # Proof found!
% 0.20/0.47  # SZS status Theorem
% 0.20/0.47  # SZS output start CNFRefutation
% 0.20/0.47  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.20/0.47  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.47  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.47  fof(t158_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))&r1_tarski(X1,k2_relat_1(X3)))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 0.20/0.47  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.20/0.47  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.47  fof(t73_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 0.20/0.47  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.20/0.47  fof(t173_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 0.20/0.47  fof(t38_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 0.20/0.47  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.20/0.47  fof(t138_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k10_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 0.20/0.47  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.20/0.47  fof(c_0_13, plain, ![X7, X8, X9]:(~r1_tarski(k2_xboole_0(X7,X8),X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.20/0.47  fof(c_0_14, plain, ![X10, X11]:(~r1_tarski(X10,X11)|k2_xboole_0(X10,X11)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.47  cnf(c_0_15, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.47  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.47  fof(c_0_17, plain, ![X32, X33]:r1_tarski(X32,k2_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.47  cnf(c_0_18, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.47  cnf(c_0_19, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.47  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))&r1_tarski(X1,k2_relat_1(X3)))=>r1_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t158_funct_1])).
% 0.20/0.47  cnf(c_0_21, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.47  fof(c_0_22, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((r1_tarski(k10_relat_1(esk4_0,esk2_0),k10_relat_1(esk4_0,esk3_0))&r1_tarski(esk2_0,k2_relat_1(esk4_0)))&~r1_tarski(esk2_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.20/0.47  fof(c_0_23, plain, ![X23, X24, X25]:(~r1_tarski(k4_xboole_0(X23,X24),X25)|r1_tarski(X23,k2_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.20/0.47  cnf(c_0_24, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X4)|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_18, c_0_21])).
% 0.20/0.47  cnf(c_0_25, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,esk2_0),k10_relat_1(esk4_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  fof(c_0_26, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.47  fof(c_0_27, plain, ![X29, X30, X31]:(~r1_tarski(X29,k2_xboole_0(X30,X31))|~r1_xboole_0(X29,X31)|r1_tarski(X29,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).
% 0.20/0.47  cnf(c_0_28, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.47  cnf(c_0_29, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,esk2_0),k2_xboole_0(X1,X2))|~r1_tarski(k10_relat_1(esk4_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.47  cnf(c_0_30, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.47  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.47  cnf(c_0_32, plain, (r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(k4_xboole_0(X1,X2),X3)))), inference(spm,[status(thm)],[c_0_28, c_0_19])).
% 0.20/0.47  fof(c_0_33, plain, ![X26, X27, X28]:(~r1_tarski(X26,X27)|~r1_xboole_0(X27,X28)|r1_xboole_0(X26,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.20/0.47  fof(c_0_34, plain, ![X36, X37]:((k10_relat_1(X37,X36)!=k1_xboole_0|r1_xboole_0(k2_relat_1(X37),X36)|~v1_relat_1(X37))&(~r1_xboole_0(k2_relat_1(X37),X36)|k10_relat_1(X37,X36)=k1_xboole_0|~v1_relat_1(X37))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t173_relat_1])])])).
% 0.20/0.47  fof(c_0_35, plain, ![X18, X19]:(~r1_tarski(X18,k4_xboole_0(X19,X18))|X18=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).
% 0.20/0.47  fof(c_0_36, plain, ![X20, X21, X22]:(~r1_tarski(X20,k2_xboole_0(X21,X22))|r1_tarski(k4_xboole_0(X20,X21),X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.20/0.47  cnf(c_0_37, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,esk2_0),X1)|~r1_tarski(k10_relat_1(esk4_0,esk3_0),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_29, c_0_16])).
% 0.20/0.47  cnf(c_0_38, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_30])).
% 0.20/0.47  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.47  cnf(c_0_40, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.47  cnf(c_0_41, plain, (r1_xboole_0(k2_relat_1(X1),X2)|k10_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.47  fof(c_0_42, plain, ![X38, X39, X40]:(~v1_relat_1(X40)|~v1_funct_1(X40)|k10_relat_1(X40,k6_subset_1(X38,X39))=k6_subset_1(k10_relat_1(X40,X38),k10_relat_1(X40,X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_funct_1])])).
% 0.20/0.47  fof(c_0_43, plain, ![X34, X35]:k6_subset_1(X34,X35)=k4_xboole_0(X34,X35), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.20/0.47  cnf(c_0_44, plain, (X1=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.47  cnf(c_0_45, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.47  cnf(c_0_46, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,esk2_0),X1)|~r1_tarski(k10_relat_1(esk4_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.47  cnf(c_0_47, plain, (r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_39, c_0_16])).
% 0.20/0.47  cnf(c_0_48, plain, (r1_xboole_0(X1,X2)|k10_relat_1(X3,X2)!=k1_xboole_0|~v1_relat_1(X3)|~r1_tarski(X1,k2_relat_1(X3))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.47  cnf(c_0_49, negated_conjecture, (r1_tarski(esk2_0,k2_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  cnf(c_0_50, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  cnf(c_0_51, plain, (k10_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.47  cnf(c_0_52, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.47  cnf(c_0_53, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,k2_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.47  cnf(c_0_54, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,esk2_0),k2_xboole_0(k10_relat_1(esk4_0,esk3_0),X1))), inference(spm,[status(thm)],[c_0_46, c_0_19])).
% 0.20/0.47  cnf(c_0_55, plain, (r1_tarski(X1,X2)|~r1_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_47, c_0_38])).
% 0.20/0.47  cnf(c_0_56, negated_conjecture, (r1_xboole_0(esk2_0,X1)|k10_relat_1(esk4_0,X1)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])])).
% 0.20/0.47  cnf(c_0_57, plain, (k10_relat_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_52])).
% 0.20/0.47  cnf(c_0_58, negated_conjecture, (k4_xboole_0(k10_relat_1(esk4_0,esk2_0),k10_relat_1(esk4_0,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.47  cnf(c_0_59, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  cnf(c_0_60, negated_conjecture, (r1_tarski(esk2_0,X1)|k10_relat_1(esk4_0,k4_xboole_0(esk2_0,X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.47  cnf(c_0_61, negated_conjecture, (k10_relat_1(esk4_0,k4_xboole_0(esk2_0,esk3_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_50])])).
% 0.20/0.47  cnf(c_0_62, negated_conjecture, (~r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), ['proof']).
% 0.20/0.47  # SZS output end CNFRefutation
% 0.20/0.47  # Proof object total steps             : 64
% 0.20/0.47  # Proof object clause steps            : 37
% 0.20/0.47  # Proof object formula steps           : 27
% 0.20/0.47  # Proof object conjectures             : 17
% 0.20/0.47  # Proof object clause conjectures      : 14
% 0.20/0.47  # Proof object formula conjectures     : 3
% 0.20/0.47  # Proof object initial clauses used    : 17
% 0.20/0.47  # Proof object initial formulas used   : 13
% 0.20/0.47  # Proof object generating inferences   : 18
% 0.20/0.47  # Proof object simplifying inferences  : 9
% 0.20/0.47  # Training examples: 0 positive, 0 negative
% 0.20/0.47  # Parsed axioms                        : 15
% 0.20/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.47  # Initial clauses                      : 24
% 0.20/0.47  # Removed in clause preprocessing      : 1
% 0.20/0.47  # Initial clauses in saturation        : 23
% 0.20/0.47  # Processed clauses                    : 1178
% 0.20/0.47  # ...of these trivial                  : 18
% 0.20/0.47  # ...subsumed                          : 770
% 0.20/0.47  # ...remaining for further processing  : 390
% 0.20/0.47  # Other redundant clauses eliminated   : 2
% 0.20/0.47  # Clauses deleted for lack of memory   : 0
% 0.20/0.47  # Backward-subsumed                    : 8
% 0.20/0.47  # Backward-rewritten                   : 11
% 0.20/0.47  # Generated clauses                    : 5334
% 0.20/0.47  # ...of the previous two non-trivial   : 4534
% 0.20/0.47  # Contextual simplify-reflections      : 0
% 0.20/0.47  # Paramodulations                      : 5332
% 0.20/0.47  # Factorizations                       : 0
% 0.20/0.47  # Equation resolutions                 : 2
% 0.20/0.47  # Propositional unsat checks           : 0
% 0.20/0.47  #    Propositional check models        : 0
% 0.20/0.47  #    Propositional check unsatisfiable : 0
% 0.20/0.47  #    Propositional clauses             : 0
% 0.20/0.47  #    Propositional clauses after purity: 0
% 0.20/0.47  #    Propositional unsat core size     : 0
% 0.20/0.47  #    Propositional preprocessing time  : 0.000
% 0.20/0.47  #    Propositional encoding time       : 0.000
% 0.20/0.47  #    Propositional solver time         : 0.000
% 0.20/0.47  #    Success case prop preproc time    : 0.000
% 0.20/0.47  #    Success case prop encoding time   : 0.000
% 0.20/0.47  #    Success case prop solver time     : 0.000
% 0.20/0.47  # Current number of processed clauses  : 347
% 0.20/0.47  #    Positive orientable unit clauses  : 46
% 0.20/0.47  #    Positive unorientable unit clauses: 0
% 0.20/0.47  #    Negative unit clauses             : 1
% 0.20/0.47  #    Non-unit-clauses                  : 300
% 0.20/0.47  # Current number of unprocessed clauses: 3351
% 0.20/0.47  # ...number of literals in the above   : 9159
% 0.20/0.47  # Current number of archived formulas  : 0
% 0.20/0.47  # Current number of archived clauses   : 42
% 0.20/0.47  # Clause-clause subsumption calls (NU) : 17227
% 0.20/0.47  # Rec. Clause-clause subsumption calls : 14964
% 0.20/0.47  # Non-unit clause-clause subsumptions  : 778
% 0.20/0.47  # Unit Clause-clause subsumption calls : 38
% 0.20/0.47  # Rewrite failures with RHS unbound    : 0
% 0.20/0.47  # BW rewrite match attempts            : 51
% 0.20/0.47  # BW rewrite match successes           : 9
% 0.20/0.47  # Condensation attempts                : 0
% 0.20/0.47  # Condensation successes               : 0
% 0.20/0.47  # Termbank termtop insertions          : 70996
% 0.20/0.47  
% 0.20/0.47  # -------------------------------------------------
% 0.20/0.47  # User time                : 0.128 s
% 0.20/0.47  # System time              : 0.006 s
% 0.20/0.47  # Total time               : 0.134 s
% 0.20/0.47  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
