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
% DateTime   : Thu Dec  3 11:12:46 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 277 expanded)
%              Number of clauses        :   40 ( 130 expanded)
%              Number of leaves         :   10 (  69 expanded)
%              Depth                    :   21
%              Number of atoms          :  145 ( 855 expanded)
%              Number of equality atoms :   45 ( 270 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_tops_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ~ ( m1_setfam_1(X2,u1_struct_0(X1))
              & X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t95_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d12_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_setfam_1(X2,X1)
    <=> r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

fof(t91_orders_1,axiom,(
    ! [X1] :
      ( ~ ( ? [X2] :
              ( X2 != k1_xboole_0
              & r2_hidden(X2,X1) )
          & k3_tarski(X1) = k1_xboole_0 )
      & ~ ( k3_tarski(X1) != k1_xboole_0
          & ! [X2] :
              ~ ( X2 != k1_xboole_0
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ~ ( m1_setfam_1(X2,u1_struct_0(X1))
                & X2 = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t5_tops_2])).

fof(c_0_11,plain,(
    ! [X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X10,X9)
        | r1_tarski(X10,X8)
        | X9 != k1_zfmisc_1(X8) )
      & ( ~ r1_tarski(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k1_zfmisc_1(X8) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | ~ r1_tarski(esk1_2(X12,X13),X12)
        | X13 = k1_zfmisc_1(X12) )
      & ( r2_hidden(esk1_2(X12,X13),X13)
        | r1_tarski(esk1_2(X12,X13),X12)
        | X13 = k1_zfmisc_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_12,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | r1_tarski(k3_tarski(X15),k3_tarski(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

fof(c_0_13,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & l1_struct_0(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
    & m1_setfam_1(esk4_0,u1_struct_0(esk3_0))
    & esk4_0 = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X17,X18] :
      ( ( ~ m1_setfam_1(X18,X17)
        | r1_tarski(X17,k3_tarski(X18)) )
      & ( ~ r1_tarski(X17,k3_tarski(X18))
        | m1_setfam_1(X18,X17) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).

cnf(c_0_19,negated_conjecture,
    ( m1_setfam_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X20,X21,X22] :
      ( ( X21 = k1_xboole_0
        | ~ r2_hidden(X21,X20)
        | k3_tarski(X20) != k1_xboole_0 )
      & ( esk2_1(X22) != k1_xboole_0
        | k3_tarski(X22) = k1_xboole_0 )
      & ( r2_hidden(esk2_1(X22),X22)
        | k3_tarski(X22) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( r1_tarski(k3_tarski(k1_xboole_0),k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_24,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_25,plain,
    ( r1_tarski(X2,k3_tarski(X1))
    | ~ m1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | k3_tarski(X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(k3_tarski(k1_xboole_0),k1_zfmisc_1(k3_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_0),k3_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0
    | k3_tarski(k1_zfmisc_1(k3_tarski(X1))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | k3_tarski(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_33,plain,(
    ! [X19] :
      ( v2_struct_0(X19)
      | ~ l1_struct_0(X19)
      | ~ v1_xboole_0(u1_struct_0(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_34,negated_conjecture,
    ( u1_struct_0(esk3_0) = k3_tarski(k1_xboole_0)
    | ~ r1_tarski(k3_tarski(k1_xboole_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0
    | r2_hidden(esk2_1(k1_zfmisc_1(k3_tarski(X1))),k1_zfmisc_1(k3_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r2_hidden(esk2_1(k1_zfmisc_1(k3_tarski(X1))),k1_zfmisc_1(k3_tarski(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_17])])).

cnf(c_0_39,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk2_1(k1_zfmisc_1(k3_tarski(X1))),k1_zfmisc_1(k3_tarski(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])]),c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk2_1(k1_zfmisc_1(k3_tarski(X1))),k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_45,negated_conjecture,
    ( esk2_1(k1_zfmisc_1(k3_tarski(X1))) = k3_tarski(X1)
    | ~ r1_tarski(k3_tarski(X1),esk2_1(k1_zfmisc_1(k3_tarski(X1)))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_44])).

cnf(c_0_46,plain,
    ( k3_tarski(X1) = k1_xboole_0
    | esk2_1(X1) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_47,negated_conjecture,
    ( esk2_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_32]),c_0_17])])).

cnf(c_0_48,negated_conjecture,
    ( k3_tarski(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k3_tarski(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | r2_hidden(esk2_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_48])).

fof(c_0_50,plain,(
    ! [X7] :
      ( ~ r1_tarski(X7,k1_xboole_0)
      | X7 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k3_tarski(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(esk2_1(k1_zfmisc_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_49])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk2_1(k1_zfmisc_1(X1)),X1)
    | r1_tarski(k3_tarski(k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( esk2_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k3_tarski(k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_55,negated_conjecture,
    ( k3_tarski(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k3_tarski(k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_54])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_55])).

cnf(c_0_57,negated_conjecture,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_56]),c_0_17])])).

cnf(c_0_58,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_57]),c_0_57]),c_0_17])])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_58]),c_0_39]),c_0_40])]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.46  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S031A
% 0.19/0.46  # and selection function PSelectStrongRRNonRROptimalLit.
% 0.19/0.46  #
% 0.19/0.46  # Preprocessing time       : 0.027 s
% 0.19/0.46  # Presaturation interreduction done
% 0.19/0.46  
% 0.19/0.46  # Proof found!
% 0.19/0.46  # SZS status Theorem
% 0.19/0.46  # SZS output start CNFRefutation
% 0.19/0.46  fof(t5_tops_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((m1_setfam_1(X2,u1_struct_0(X1))&X2=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tops_2)).
% 0.19/0.46  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.19/0.46  fof(t95_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 0.19/0.46  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.46  fof(d12_setfam_1, axiom, ![X1, X2]:(m1_setfam_1(X2,X1)<=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 0.19/0.46  fof(t91_orders_1, axiom, ![X1]:(~((?[X2]:(X2!=k1_xboole_0&r2_hidden(X2,X1))&k3_tarski(X1)=k1_xboole_0))&~((k3_tarski(X1)!=k1_xboole_0&![X2]:~((X2!=k1_xboole_0&r2_hidden(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 0.19/0.46  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.46  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.46  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.46  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.19/0.46  fof(c_0_10, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((m1_setfam_1(X2,u1_struct_0(X1))&X2=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t5_tops_2])).
% 0.19/0.46  fof(c_0_11, plain, ![X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X10,X9)|r1_tarski(X10,X8)|X9!=k1_zfmisc_1(X8))&(~r1_tarski(X11,X8)|r2_hidden(X11,X9)|X9!=k1_zfmisc_1(X8)))&((~r2_hidden(esk1_2(X12,X13),X13)|~r1_tarski(esk1_2(X12,X13),X12)|X13=k1_zfmisc_1(X12))&(r2_hidden(esk1_2(X12,X13),X13)|r1_tarski(esk1_2(X12,X13),X12)|X13=k1_zfmisc_1(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.46  fof(c_0_12, plain, ![X15, X16]:(~r1_tarski(X15,X16)|r1_tarski(k3_tarski(X15),k3_tarski(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).
% 0.19/0.46  fof(c_0_13, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.46  fof(c_0_14, negated_conjecture, ((~v2_struct_0(esk3_0)&l1_struct_0(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))&(m1_setfam_1(esk4_0,u1_struct_0(esk3_0))&esk4_0=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.19/0.46  cnf(c_0_15, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.46  cnf(c_0_16, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.46  cnf(c_0_17, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.46  fof(c_0_18, plain, ![X17, X18]:((~m1_setfam_1(X18,X17)|r1_tarski(X17,k3_tarski(X18)))&(~r1_tarski(X17,k3_tarski(X18))|m1_setfam_1(X18,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).
% 0.19/0.46  cnf(c_0_19, negated_conjecture, (m1_setfam_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.46  cnf(c_0_20, negated_conjecture, (esk4_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.46  fof(c_0_21, plain, ![X20, X21, X22]:((X21=k1_xboole_0|~r2_hidden(X21,X20)|k3_tarski(X20)!=k1_xboole_0)&((esk2_1(X22)!=k1_xboole_0|k3_tarski(X22)=k1_xboole_0)&(r2_hidden(esk2_1(X22),X22)|k3_tarski(X22)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).
% 0.19/0.46  cnf(c_0_22, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_15])).
% 0.19/0.46  cnf(c_0_23, plain, (r1_tarski(k3_tarski(k1_xboole_0),k3_tarski(X1))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.46  fof(c_0_24, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.46  cnf(c_0_25, plain, (r1_tarski(X2,k3_tarski(X1))|~m1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.46  cnf(c_0_26, negated_conjecture, (m1_setfam_1(k1_xboole_0,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.46  cnf(c_0_27, plain, (X1=k1_xboole_0|~r2_hidden(X1,X2)|k3_tarski(X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.46  cnf(c_0_28, plain, (r2_hidden(k3_tarski(k1_xboole_0),k1_zfmisc_1(k3_tarski(X1)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.46  cnf(c_0_29, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.46  cnf(c_0_30, negated_conjecture, (r1_tarski(u1_struct_0(esk3_0),k3_tarski(k1_xboole_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.46  cnf(c_0_31, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0|k3_tarski(k1_zfmisc_1(k3_tarski(X1)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.46  cnf(c_0_32, plain, (r2_hidden(esk2_1(X1),X1)|k3_tarski(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.46  fof(c_0_33, plain, ![X19]:(v2_struct_0(X19)|~l1_struct_0(X19)|~v1_xboole_0(u1_struct_0(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.46  cnf(c_0_34, negated_conjecture, (u1_struct_0(esk3_0)=k3_tarski(k1_xboole_0)|~r1_tarski(k3_tarski(k1_xboole_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.46  cnf(c_0_35, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0|r2_hidden(esk2_1(k1_zfmisc_1(k3_tarski(X1))),k1_zfmisc_1(k3_tarski(X1)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.46  cnf(c_0_36, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.46  cnf(c_0_37, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.46  cnf(c_0_38, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r2_hidden(esk2_1(k1_zfmisc_1(k3_tarski(X1))),k1_zfmisc_1(k3_tarski(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_17])])).
% 0.19/0.46  cnf(c_0_39, negated_conjecture, (l1_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.46  cnf(c_0_40, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.46  cnf(c_0_41, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.46  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_36])).
% 0.19/0.46  cnf(c_0_43, negated_conjecture, (r2_hidden(esk2_1(k1_zfmisc_1(k3_tarski(X1))),k1_zfmisc_1(k3_tarski(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40])]), c_0_41])).
% 0.19/0.46  cnf(c_0_44, negated_conjecture, (r1_tarski(esk2_1(k1_zfmisc_1(k3_tarski(X1))),k3_tarski(X1))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.46  cnf(c_0_45, negated_conjecture, (esk2_1(k1_zfmisc_1(k3_tarski(X1)))=k3_tarski(X1)|~r1_tarski(k3_tarski(X1),esk2_1(k1_zfmisc_1(k3_tarski(X1))))), inference(spm,[status(thm)],[c_0_29, c_0_44])).
% 0.19/0.46  cnf(c_0_46, plain, (k3_tarski(X1)=k1_xboole_0|esk2_1(X1)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.46  cnf(c_0_47, negated_conjecture, (esk2_1(k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_32]), c_0_17])])).
% 0.19/0.46  cnf(c_0_48, negated_conjecture, (k3_tarski(k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.46  cnf(c_0_49, negated_conjecture, (r2_hidden(k3_tarski(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))|r2_hidden(esk2_1(X1),X1)), inference(spm,[status(thm)],[c_0_28, c_0_48])).
% 0.19/0.46  fof(c_0_50, plain, ![X7]:(~r1_tarski(X7,k1_xboole_0)|X7=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.19/0.46  cnf(c_0_51, negated_conjecture, (r2_hidden(k3_tarski(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))|r1_tarski(esk2_1(k1_zfmisc_1(X1)),X1)), inference(spm,[status(thm)],[c_0_42, c_0_49])).
% 0.19/0.46  cnf(c_0_52, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.46  cnf(c_0_53, negated_conjecture, (r1_tarski(esk2_1(k1_zfmisc_1(X1)),X1)|r1_tarski(k3_tarski(k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_51])).
% 0.19/0.46  cnf(c_0_54, negated_conjecture, (esk2_1(k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|r1_tarski(k3_tarski(k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.46  cnf(c_0_55, negated_conjecture, (k3_tarski(k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|r1_tarski(k3_tarski(k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_54])).
% 0.19/0.46  cnf(c_0_56, negated_conjecture, (r1_tarski(k3_tarski(k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_23, c_0_55])).
% 0.19/0.46  cnf(c_0_57, negated_conjecture, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_56]), c_0_17])])).
% 0.19/0.46  cnf(c_0_58, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_57]), c_0_57]), c_0_17])])).
% 0.19/0.46  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_58]), c_0_39]), c_0_40])]), c_0_41]), ['proof']).
% 0.19/0.46  # SZS output end CNFRefutation
% 0.19/0.46  # Proof object total steps             : 60
% 0.19/0.46  # Proof object clause steps            : 40
% 0.19/0.46  # Proof object formula steps           : 20
% 0.19/0.46  # Proof object conjectures             : 25
% 0.19/0.46  # Proof object clause conjectures      : 22
% 0.19/0.46  # Proof object formula conjectures     : 3
% 0.19/0.46  # Proof object initial clauses used    : 16
% 0.19/0.46  # Proof object initial formulas used   : 10
% 0.19/0.46  # Proof object generating inferences   : 20
% 0.19/0.46  # Proof object simplifying inferences  : 21
% 0.19/0.46  # Training examples: 0 positive, 0 negative
% 0.19/0.46  # Parsed axioms                        : 10
% 0.19/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.46  # Initial clauses                      : 22
% 0.19/0.46  # Removed in clause preprocessing      : 0
% 0.19/0.46  # Initial clauses in saturation        : 22
% 0.19/0.46  # Processed clauses                    : 310
% 0.19/0.46  # ...of these trivial                  : 4
% 0.19/0.46  # ...subsumed                          : 76
% 0.19/0.46  # ...remaining for further processing  : 230
% 0.19/0.46  # Other redundant clauses eliminated   : 246
% 0.19/0.46  # Clauses deleted for lack of memory   : 0
% 0.19/0.46  # Backward-subsumed                    : 13
% 0.19/0.46  # Backward-rewritten                   : 104
% 0.19/0.46  # Generated clauses                    : 5509
% 0.19/0.46  # ...of the previous two non-trivial   : 4567
% 0.19/0.46  # Contextual simplify-reflections      : 0
% 0.19/0.46  # Paramodulations                      : 5261
% 0.19/0.46  # Factorizations                       : 2
% 0.19/0.46  # Equation resolutions                 : 246
% 0.19/0.46  # Propositional unsat checks           : 0
% 0.19/0.46  #    Propositional check models        : 0
% 0.19/0.46  #    Propositional check unsatisfiable : 0
% 0.19/0.46  #    Propositional clauses             : 0
% 0.19/0.46  #    Propositional clauses after purity: 0
% 0.19/0.46  #    Propositional unsat core size     : 0
% 0.19/0.46  #    Propositional preprocessing time  : 0.000
% 0.19/0.46  #    Propositional encoding time       : 0.000
% 0.19/0.46  #    Propositional solver time         : 0.000
% 0.19/0.46  #    Success case prop preproc time    : 0.000
% 0.19/0.46  #    Success case prop encoding time   : 0.000
% 0.19/0.46  #    Success case prop solver time     : 0.000
% 0.19/0.46  # Current number of processed clauses  : 88
% 0.19/0.46  #    Positive orientable unit clauses  : 15
% 0.19/0.46  #    Positive unorientable unit clauses: 0
% 0.19/0.46  #    Negative unit clauses             : 1
% 0.19/0.46  #    Non-unit-clauses                  : 72
% 0.19/0.46  # Current number of unprocessed clauses: 4276
% 0.19/0.46  # ...number of literals in the above   : 22576
% 0.19/0.46  # Current number of archived formulas  : 0
% 0.19/0.46  # Current number of archived clauses   : 138
% 0.19/0.46  # Clause-clause subsumption calls (NU) : 2613
% 0.19/0.46  # Rec. Clause-clause subsumption calls : 1568
% 0.19/0.46  # Non-unit clause-clause subsumptions  : 85
% 0.19/0.46  # Unit Clause-clause subsumption calls : 42
% 0.19/0.46  # Rewrite failures with RHS unbound    : 0
% 0.19/0.46  # BW rewrite match attempts            : 15
% 0.19/0.46  # BW rewrite match successes           : 11
% 0.19/0.46  # Condensation attempts                : 0
% 0.19/0.46  # Condensation successes               : 0
% 0.19/0.46  # Termbank termtop insertions          : 87504
% 0.19/0.46  
% 0.19/0.46  # -------------------------------------------------
% 0.19/0.46  # User time                : 0.111 s
% 0.19/0.46  # System time              : 0.007 s
% 0.19/0.46  # Total time               : 0.118 s
% 0.19/0.46  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
