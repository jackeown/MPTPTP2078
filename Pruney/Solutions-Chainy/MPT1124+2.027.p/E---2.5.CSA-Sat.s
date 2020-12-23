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
% DateTime   : Thu Dec  3 11:09:20 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 124 expanded)
%              Number of clauses        :   32 (  50 expanded)
%              Number of leaves         :   11 (  34 expanded)
%              Depth                    :    4
%              Number of atoms          :  142 ( 352 expanded)
%              Number of equality atoms :    6 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t55_pre_topc,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_11,plain,(
    ! [X21,X22,X23] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_pre_topc(X22,X21)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

fof(c_0_12,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_13,plain,(
    ! [X7,X8,X9] :
      ( ( r2_hidden(X7,X9)
        | ~ r1_tarski(k2_tarski(X7,X8),X9) )
      & ( r2_hidden(X8,X9)
        | ~ r1_tarski(k2_tarski(X7,X8),X9) )
      & ( ~ r2_hidden(X7,X9)
        | ~ r2_hidden(X8,X9)
        | r1_tarski(k2_tarski(X7,X8),X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_14,plain,(
    ! [X5,X6] : k1_enumset1(X5,X5,X6) = k2_tarski(X5,X6) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X14,X15)
      | v1_xboole_0(X15)
      | r2_hidden(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_16,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,X11)
      | m1_subset_1(k1_tarski(X10),k1_zfmisc_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

fof(c_0_17,plain,(
    ! [X4] : k2_tarski(X4,X4) = k1_tarski(X4) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t55_pre_topc])).

cnf(c_0_19,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_21,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_24,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & ~ m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

fof(c_0_27,plain,(
    ! [X19,X20] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_pre_topc(X20,X19)
      | l1_pre_topc(X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X1,u1_struct_0(X3)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20]),
    [final]).

cnf(c_0_29,plain,
    ( r1_tarski(k1_enumset1(X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22]),
    [final]).

cnf(c_0_30,plain,
    ( v1_xboole_0(k1_zfmisc_1(X1))
    | r2_hidden(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_20]),
    [final]).

cnf(c_0_31,plain,
    ( m1_subset_1(k1_enumset1(X1,X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_22]),
    [final]).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_36,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,X13)
      | m1_subset_1(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_37,plain,(
    ! [X18] :
      ( ~ l1_pre_topc(X18)
      | l1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_38,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_41,plain,
    ( m1_subset_1(k1_enumset1(X1,X1,X2),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X4,X3)
    | ~ l1_pre_topc(X3)
    | ~ r2_hidden(X2,u1_struct_0(X4))
    | ~ r2_hidden(X1,u1_struct_0(X4)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29]),
    [final]).

cnf(c_0_42,plain,
    ( v1_xboole_0(k1_zfmisc_1(X1))
    | r2_hidden(k1_enumset1(X2,X2,X3),k1_zfmisc_1(X1))
    | ~ r2_hidden(X3,X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29]),
    [final]).

cnf(c_0_43,plain,
    ( m1_subset_1(k1_enumset1(X1,X1,X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_struct_0(X3)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_31]),
    [final]).

cnf(c_0_44,plain,
    ( r1_tarski(k1_enumset1(X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31]),
    [final]).

cnf(c_0_45,plain,
    ( v1_xboole_0(k1_zfmisc_1(X1))
    | r2_hidden(k1_enumset1(X2,X2,X2),k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_31]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | r2_hidden(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_33]),
    [final]).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_enumset1(X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[c_0_34,c_0_22]),
    [final]).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_enumset1(X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_22]),
    [final]).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36]),
    [final]).

cnf(c_0_50,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( ~ m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:09:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # No proof found!
% 0.20/0.38  # SZS status CounterSatisfiable
% 0.20/0.38  # SZS output start Saturation
% 0.20/0.38  fof(t39_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.20/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.38  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.20/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.38  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 0.20/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.38  fof(t55_pre_topc, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.20/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.38  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.38  fof(c_0_11, plain, ![X21, X22, X23]:(~l1_pre_topc(X21)|(~m1_pre_topc(X22,X21)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).
% 0.20/0.38  fof(c_0_12, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.38  fof(c_0_13, plain, ![X7, X8, X9]:(((r2_hidden(X7,X9)|~r1_tarski(k2_tarski(X7,X8),X9))&(r2_hidden(X8,X9)|~r1_tarski(k2_tarski(X7,X8),X9)))&(~r2_hidden(X7,X9)|~r2_hidden(X8,X9)|r1_tarski(k2_tarski(X7,X8),X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.20/0.38  fof(c_0_14, plain, ![X5, X6]:k1_enumset1(X5,X5,X6)=k2_tarski(X5,X6), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.38  fof(c_0_15, plain, ![X14, X15]:(~m1_subset_1(X14,X15)|(v1_xboole_0(X15)|r2_hidden(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.38  fof(c_0_16, plain, ![X10, X11]:(~r2_hidden(X10,X11)|m1_subset_1(k1_tarski(X10),k1_zfmisc_1(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.20/0.38  fof(c_0_17, plain, ![X4]:k2_tarski(X4,X4)=k1_tarski(X4), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.38  fof(c_0_18, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1)))))), inference(assume_negation,[status(cth)],[t55_pre_topc])).
% 0.20/0.38  cnf(c_0_19, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.20/0.38  cnf(c_0_20, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.20/0.38  cnf(c_0_21, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_23, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.20/0.38  cnf(c_0_24, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  fof(c_0_26, negated_conjecture, ((~v2_struct_0(esk1_0)&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&~m1_subset_1(esk3_0,u1_struct_0(esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 0.20/0.38  fof(c_0_27, plain, ![X19, X20]:(~l1_pre_topc(X19)|(~m1_pre_topc(X20,X19)|l1_pre_topc(X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.38  cnf(c_0_28, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)|~r1_tarski(X1,u1_struct_0(X3))), inference(spm,[status(thm)],[c_0_19, c_0_20]), ['final']).
% 0.20/0.38  cnf(c_0_29, plain, (r1_tarski(k1_enumset1(X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22]), ['final']).
% 0.20/0.38  cnf(c_0_30, plain, (v1_xboole_0(k1_zfmisc_1(X1))|r2_hidden(X2,k1_zfmisc_1(X1))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_23, c_0_20]), ['final']).
% 0.20/0.38  cnf(c_0_31, plain, (m1_subset_1(k1_enumset1(X1,X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_22]), ['final']).
% 0.20/0.38  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.20/0.38  cnf(c_0_34, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_35, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  fof(c_0_36, plain, ![X12, X13]:(~r2_hidden(X12,X13)|m1_subset_1(X12,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.38  fof(c_0_37, plain, ![X18]:(~l1_pre_topc(X18)|l1_struct_0(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.38  cnf(c_0_38, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.20/0.38  cnf(c_0_40, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.20/0.38  cnf(c_0_41, plain, (m1_subset_1(k1_enumset1(X1,X1,X2),k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X4,X3)|~l1_pre_topc(X3)|~r2_hidden(X2,u1_struct_0(X4))|~r2_hidden(X1,u1_struct_0(X4))), inference(spm,[status(thm)],[c_0_28, c_0_29]), ['final']).
% 0.20/0.38  cnf(c_0_42, plain, (v1_xboole_0(k1_zfmisc_1(X1))|r2_hidden(k1_enumset1(X2,X2,X3),k1_zfmisc_1(X1))|~r2_hidden(X3,X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_30, c_0_29]), ['final']).
% 0.20/0.38  cnf(c_0_43, plain, (m1_subset_1(k1_enumset1(X1,X1,X1),k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)|~r2_hidden(X1,u1_struct_0(X3))), inference(spm,[status(thm)],[c_0_19, c_0_31]), ['final']).
% 0.20/0.38  cnf(c_0_44, plain, (r1_tarski(k1_enumset1(X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_31]), ['final']).
% 0.20/0.38  cnf(c_0_45, plain, (v1_xboole_0(k1_zfmisc_1(X1))|r2_hidden(k1_enumset1(X2,X2,X2),k1_zfmisc_1(X1))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_23, c_0_31]), ['final']).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|r2_hidden(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_23, c_0_33]), ['final']).
% 0.20/0.38  cnf(c_0_47, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_enumset1(X1,X1,X3),X2)), inference(rw,[status(thm)],[c_0_34, c_0_22]), ['final']).
% 0.20/0.38  cnf(c_0_48, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_enumset1(X3,X3,X1),X2)), inference(rw,[status(thm)],[c_0_35, c_0_22]), ['final']).
% 0.20/0.38  cnf(c_0_49, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36]), ['final']).
% 0.20/0.38  cnf(c_0_50, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_37]), ['final']).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (~m1_subset_1(esk3_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.20/0.38  cnf(c_0_54, negated_conjecture, (l1_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])]), ['final']).
% 0.20/0.38  # SZS output end Saturation
% 0.20/0.38  # Proof object total steps             : 55
% 0.20/0.38  # Proof object clause steps            : 32
% 0.20/0.38  # Proof object formula steps           : 23
% 0.20/0.38  # Proof object conjectures             : 11
% 0.20/0.38  # Proof object clause conjectures      : 8
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 19
% 0.20/0.38  # Proof object initial formulas used   : 11
% 0.20/0.38  # Proof object generating inferences   : 9
% 0.20/0.38  # Proof object simplifying inferences  : 7
% 0.20/0.38  # Parsed axioms                        : 11
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 19
% 0.20/0.38  # Removed in clause preprocessing      : 2
% 0.20/0.38  # Initial clauses in saturation        : 17
% 0.20/0.38  # Processed clauses                    : 45
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 2
% 0.20/0.38  # ...remaining for further processing  : 43
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 0
% 0.20/0.38  # Generated clauses                    : 16
% 0.20/0.38  # ...of the previous two non-trivial   : 11
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 16
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 26
% 0.20/0.38  #    Positive orientable unit clauses  : 4
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 3
% 0.20/0.38  #    Non-unit-clauses                  : 19
% 0.20/0.38  # Current number of unprocessed clauses: 0
% 0.20/0.38  # ...number of literals in the above   : 0
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 19
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 62
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 42
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.20/0.38  # Unit Clause-clause subsumption calls : 2
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 0
% 0.20/0.38  # BW rewrite match successes           : 0
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 1451
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.028 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.032 s
% 0.20/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
