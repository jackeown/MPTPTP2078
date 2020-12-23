%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:42 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 222 expanded)
%              Number of clauses        :   36 (  92 expanded)
%              Number of leaves         :   12 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  191 ( 710 expanded)
%              Number of equality atoms :   34 ( 139 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t10_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
           => X1 = k1_wellord1(k1_wellord2(X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(t11_wellord2,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

fof(t7_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v2_wellord1(k1_wellord2(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

fof(d1_wellord2,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k1_wellord2(X1)
      <=> ( k3_relat_1(X2) = X1
          & ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1) )
             => ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r1_tarski(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(t57_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(t8_wellord2,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(t50_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r4_wellord1(X1,X2)
           => r4_wellord1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(c_0_12,plain,(
    ! [X25,X26] :
      ( ~ v3_ordinal1(X25)
      | ~ v3_ordinal1(X26)
      | ~ r2_hidden(X25,X26)
      | X25 = k1_wellord1(k1_wellord2(X26),X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).

fof(c_0_13,plain,(
    ! [X10,X11] :
      ( ~ v3_ordinal1(X11)
      | ~ r2_hidden(X10,X11)
      | v3_ordinal1(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
             => X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t11_wellord2])).

cnf(c_0_15,plain,
    ( X1 = k1_wellord1(k1_wellord2(X2),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,negated_conjecture,
    ( v3_ordinal1(esk4_0)
    & v3_ordinal1(esk5_0)
    & r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk5_0))
    & esk4_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_18,plain,(
    ! [X27] :
      ( ~ v3_ordinal1(X27)
      | v2_wellord1(k1_wellord2(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).

fof(c_0_19,plain,(
    ! [X18,X19,X20,X21] :
      ( ( k3_relat_1(X19) = X18
        | X19 != k1_wellord2(X18)
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(X20,X21),X19)
        | r1_tarski(X20,X21)
        | ~ r2_hidden(X20,X18)
        | ~ r2_hidden(X21,X18)
        | X19 != k1_wellord2(X18)
        | ~ v1_relat_1(X19) )
      & ( ~ r1_tarski(X20,X21)
        | r2_hidden(k4_tarski(X20,X21),X19)
        | ~ r2_hidden(X20,X18)
        | ~ r2_hidden(X21,X18)
        | X19 != k1_wellord2(X18)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk2_2(X18,X19),X18)
        | k3_relat_1(X19) != X18
        | X19 = k1_wellord2(X18)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk3_2(X18,X19),X18)
        | k3_relat_1(X19) != X18
        | X19 = k1_wellord2(X18)
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X18,X19),esk3_2(X18,X19)),X19)
        | ~ r1_tarski(esk2_2(X18,X19),esk3_2(X18,X19))
        | k3_relat_1(X19) != X18
        | X19 = k1_wellord2(X18)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk2_2(X18,X19),esk3_2(X18,X19)),X19)
        | r1_tarski(esk2_2(X18,X19),esk3_2(X18,X19))
        | k3_relat_1(X19) != X18
        | X19 = k1_wellord2(X18)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_20,plain,(
    ! [X24] : v1_relat_1(k1_wellord2(X24)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_21,plain,(
    ! [X5] :
      ( ( v1_ordinal1(X5)
        | ~ v3_ordinal1(X5) )
      & ( v2_ordinal1(X5)
        | ~ v3_ordinal1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

fof(c_0_22,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | ~ v2_wellord1(X16)
      | ~ r2_hidden(X17,k3_relat_1(X16))
      | ~ r4_wellord1(X16,k2_wellord1(X16,k1_wellord1(X16,X17))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).

cnf(c_0_23,plain,
    ( k1_wellord1(k1_wellord2(X1),X2) = X2
    | ~ r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1) ),
    inference(csr,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( v3_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( v2_wellord1(k1_wellord2(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_ordinal1(X6)
        | ~ r2_hidden(X7,X6)
        | r1_tarski(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_ordinal1(X8) )
      & ( ~ r1_tarski(esk1_1(X8),X8)
        | v1_ordinal1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

cnf(c_0_29,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X12,X13] :
      ( ~ v3_ordinal1(X12)
      | ~ v3_ordinal1(X13)
      | r2_hidden(X12,X13)
      | X12 = X13
      | r2_hidden(X13,X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

cnf(c_0_31,plain,
    ( ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk5_0),X1) = X1
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v2_wellord1(k1_wellord2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_34,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_26]),c_0_27])])).

fof(c_0_35,plain,(
    ! [X28,X29] :
      ( ~ r1_tarski(X28,X29)
      | k2_wellord1(k1_wellord2(X29),X28) = k1_wellord2(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).

cnf(c_0_36,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( v1_ordinal1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_24])).

fof(c_0_38,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | ~ v1_relat_1(X15)
      | ~ r4_wellord1(X14,X15)
      | r4_wellord1(X15,X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( ~ r4_wellord1(k1_wellord2(esk5_0),k2_wellord1(k1_wellord2(esk5_0),X1))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_27]),c_0_34])])).

cnf(c_0_41,plain,
    ( k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(X1,esk5_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r4_wellord1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_45,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( X1 = esk5_0
    | r2_hidden(X1,esk5_0)
    | r2_hidden(esk5_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_24])).

cnf(c_0_47,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( ~ r4_wellord1(k1_wellord2(esk5_0),k1_wellord2(X1))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk5_0),k1_wellord2(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_27]),c_0_27])])).

cnf(c_0_50,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk4_0),X1) = X1
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( v2_wellord1(k1_wellord2(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_45]),c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( ~ r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(esk4_0),X1))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_50]),c_0_51]),c_0_27]),c_0_34])])).

cnf(c_0_55,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(X1),esk5_0))
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( v1_ordinal1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_56])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:19:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.12/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t10_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>X1=k1_wellord1(k1_wellord2(X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_wellord2)).
% 0.12/0.37  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 0.12/0.37  fof(t11_wellord2, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_wellord2)).
% 0.12/0.37  fof(t7_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>v2_wellord1(k1_wellord2(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_wellord2)).
% 0.12/0.37  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.12/0.37  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.12/0.37  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 0.12/0.37  fof(t57_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)=>![X2]:~((r2_hidden(X2,k3_relat_1(X1))&r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_wellord1)).
% 0.12/0.37  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 0.12/0.37  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 0.12/0.37  fof(t8_wellord2, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 0.12/0.37  fof(t50_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r4_wellord1(X1,X2)=>r4_wellord1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_wellord1)).
% 0.12/0.37  fof(c_0_12, plain, ![X25, X26]:(~v3_ordinal1(X25)|(~v3_ordinal1(X26)|(~r2_hidden(X25,X26)|X25=k1_wellord1(k1_wellord2(X26),X25)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).
% 0.12/0.37  fof(c_0_13, plain, ![X10, X11]:(~v3_ordinal1(X11)|(~r2_hidden(X10,X11)|v3_ordinal1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 0.12/0.37  fof(c_0_14, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2)))), inference(assume_negation,[status(cth)],[t11_wellord2])).
% 0.12/0.37  cnf(c_0_15, plain, (X1=k1_wellord1(k1_wellord2(X2),X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_16, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  fof(c_0_17, negated_conjecture, (v3_ordinal1(esk4_0)&(v3_ordinal1(esk5_0)&(r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk5_0))&esk4_0!=esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.12/0.37  fof(c_0_18, plain, ![X27]:(~v3_ordinal1(X27)|v2_wellord1(k1_wellord2(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).
% 0.12/0.37  fof(c_0_19, plain, ![X18, X19, X20, X21]:(((k3_relat_1(X19)=X18|X19!=k1_wellord2(X18)|~v1_relat_1(X19))&((~r2_hidden(k4_tarski(X20,X21),X19)|r1_tarski(X20,X21)|(~r2_hidden(X20,X18)|~r2_hidden(X21,X18))|X19!=k1_wellord2(X18)|~v1_relat_1(X19))&(~r1_tarski(X20,X21)|r2_hidden(k4_tarski(X20,X21),X19)|(~r2_hidden(X20,X18)|~r2_hidden(X21,X18))|X19!=k1_wellord2(X18)|~v1_relat_1(X19))))&(((r2_hidden(esk2_2(X18,X19),X18)|k3_relat_1(X19)!=X18|X19=k1_wellord2(X18)|~v1_relat_1(X19))&(r2_hidden(esk3_2(X18,X19),X18)|k3_relat_1(X19)!=X18|X19=k1_wellord2(X18)|~v1_relat_1(X19)))&((~r2_hidden(k4_tarski(esk2_2(X18,X19),esk3_2(X18,X19)),X19)|~r1_tarski(esk2_2(X18,X19),esk3_2(X18,X19))|k3_relat_1(X19)!=X18|X19=k1_wellord2(X18)|~v1_relat_1(X19))&(r2_hidden(k4_tarski(esk2_2(X18,X19),esk3_2(X18,X19)),X19)|r1_tarski(esk2_2(X18,X19),esk3_2(X18,X19))|k3_relat_1(X19)!=X18|X19=k1_wellord2(X18)|~v1_relat_1(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.12/0.37  fof(c_0_20, plain, ![X24]:v1_relat_1(k1_wellord2(X24)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.12/0.37  fof(c_0_21, plain, ![X5]:((v1_ordinal1(X5)|~v3_ordinal1(X5))&(v2_ordinal1(X5)|~v3_ordinal1(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 0.12/0.37  fof(c_0_22, plain, ![X16, X17]:(~v1_relat_1(X16)|(~v2_wellord1(X16)|(~r2_hidden(X17,k3_relat_1(X16))|~r4_wellord1(X16,k2_wellord1(X16,k1_wellord1(X16,X17)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).
% 0.12/0.37  cnf(c_0_23, plain, (k1_wellord1(k1_wellord2(X1),X2)=X2|~r2_hidden(X2,X1)|~v3_ordinal1(X1)), inference(csr,[status(thm)],[c_0_15, c_0_16])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (v3_ordinal1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_25, plain, (v2_wellord1(k1_wellord2(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.37  cnf(c_0_26, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.37  cnf(c_0_27, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  fof(c_0_28, plain, ![X6, X7, X8]:((~v1_ordinal1(X6)|(~r2_hidden(X7,X6)|r1_tarski(X7,X6)))&((r2_hidden(esk1_1(X8),X8)|v1_ordinal1(X8))&(~r1_tarski(esk1_1(X8),X8)|v1_ordinal1(X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 0.12/0.37  cnf(c_0_29, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.37  fof(c_0_30, plain, ![X12, X13]:(~v3_ordinal1(X12)|(~v3_ordinal1(X13)|(r2_hidden(X12,X13)|X12=X13|r2_hidden(X13,X12)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 0.12/0.37  cnf(c_0_31, plain, (~v1_relat_1(X1)|~v2_wellord1(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (k1_wellord1(k1_wellord2(esk5_0),X1)=X1|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, (v2_wellord1(k1_wellord2(esk5_0))), inference(spm,[status(thm)],[c_0_25, c_0_24])).
% 0.12/0.37  cnf(c_0_34, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_26]), c_0_27])])).
% 0.12/0.37  fof(c_0_35, plain, ![X28, X29]:(~r1_tarski(X28,X29)|k2_wellord1(k1_wellord2(X29),X28)=k1_wellord2(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).
% 0.12/0.37  cnf(c_0_36, plain, (r1_tarski(X2,X1)|~v1_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (v1_ordinal1(esk5_0)), inference(spm,[status(thm)],[c_0_29, c_0_24])).
% 0.12/0.37  fof(c_0_38, plain, ![X14, X15]:(~v1_relat_1(X14)|(~v1_relat_1(X15)|(~r4_wellord1(X14,X15)|r4_wellord1(X15,X14)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).
% 0.12/0.37  cnf(c_0_39, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, (~r4_wellord1(k1_wellord2(esk5_0),k2_wellord1(k1_wellord2(esk5_0),X1))|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_27]), c_0_34])])).
% 0.12/0.37  cnf(c_0_41, plain, (k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, (r1_tarski(X1,esk5_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.12/0.37  cnf(c_0_43, plain, (r4_wellord1(X2,X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r4_wellord1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_45, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, (X1=esk5_0|r2_hidden(X1,esk5_0)|r2_hidden(esk5_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_24])).
% 0.12/0.37  cnf(c_0_47, negated_conjecture, (esk4_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_48, negated_conjecture, (~r4_wellord1(k1_wellord2(esk5_0),k1_wellord2(X1))|~r2_hidden(X1,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.12/0.37  cnf(c_0_49, negated_conjecture, (r4_wellord1(k1_wellord2(esk5_0),k1_wellord2(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_27]), c_0_27])])).
% 0.12/0.37  cnf(c_0_50, negated_conjecture, (k1_wellord1(k1_wellord2(esk4_0),X1)=X1|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_45])).
% 0.12/0.37  cnf(c_0_51, negated_conjecture, (v2_wellord1(k1_wellord2(esk4_0))), inference(spm,[status(thm)],[c_0_25, c_0_45])).
% 0.12/0.37  cnf(c_0_52, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|r2_hidden(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_45]), c_0_47])).
% 0.12/0.37  cnf(c_0_53, negated_conjecture, (~r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.12/0.37  cnf(c_0_54, negated_conjecture, (~r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(esk4_0),X1))|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_50]), c_0_51]), c_0_27]), c_0_34])])).
% 0.12/0.37  cnf(c_0_55, negated_conjecture, (r4_wellord1(k1_wellord2(esk4_0),k2_wellord1(k1_wellord2(X1),esk5_0))|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_44, c_0_41])).
% 0.12/0.37  cnf(c_0_56, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(sr,[status(thm)],[c_0_52, c_0_53])).
% 0.12/0.37  cnf(c_0_57, negated_conjecture, (v1_ordinal1(esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_45])).
% 0.12/0.37  cnf(c_0_58, negated_conjecture, (~r1_tarski(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 0.12/0.37  cnf(c_0_59, negated_conjecture, (r1_tarski(X1,esk4_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_57])).
% 0.12/0.37  cnf(c_0_60, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_56])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 61
% 0.12/0.37  # Proof object clause steps            : 36
% 0.12/0.37  # Proof object formula steps           : 25
% 0.12/0.37  # Proof object conjectures             : 26
% 0.12/0.37  # Proof object clause conjectures      : 23
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 15
% 0.12/0.37  # Proof object initial formulas used   : 12
% 0.12/0.37  # Proof object generating inferences   : 18
% 0.12/0.37  # Proof object simplifying inferences  : 22
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 12
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 24
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 24
% 0.12/0.37  # Processed clauses                    : 83
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 3
% 0.12/0.37  # ...remaining for further processing  : 80
% 0.12/0.37  # Other redundant clauses eliminated   : 7
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 82
% 0.12/0.37  # ...of the previous two non-trivial   : 68
% 0.12/0.37  # Contextual simplify-reflections      : 2
% 0.12/0.37  # Paramodulations                      : 74
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 7
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 48
% 0.12/0.37  #    Positive orientable unit clauses  : 13
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 3
% 0.12/0.37  #    Non-unit-clauses                  : 32
% 0.12/0.37  # Current number of unprocessed clauses: 33
% 0.12/0.37  # ...number of literals in the above   : 107
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 25
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 158
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 90
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 4
% 0.12/0.37  # Unit Clause-clause subsumption calls : 37
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 0
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 3251
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.029 s
% 0.12/0.37  # System time              : 0.006 s
% 0.12/0.37  # Total time               : 0.035 s
% 0.12/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
