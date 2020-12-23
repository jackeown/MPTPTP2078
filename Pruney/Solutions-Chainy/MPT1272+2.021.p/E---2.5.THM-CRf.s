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
% DateTime   : Thu Dec  3 11:12:17 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 113 expanded)
%              Number of clauses        :   33 (  46 expanded)
%              Number of leaves         :    9 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  140 ( 343 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t91_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tops_1(X2,X1)
           => v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(d5_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tops_1(X2,X1)
          <=> v2_tops_1(k2_pre_topc(X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(t88_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> r1_tarski(X2,k2_tops_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t72_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X2)),k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_1)).

fof(d4_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_tops_1(X2,X1)
             => v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t91_tops_1])).

fof(c_0_10,plain,(
    ! [X11,X12] :
      ( ~ l1_pre_topc(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
      | r1_tarski(X12,k2_pre_topc(X11,X12)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

fof(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v3_tops_1(esk2_0,esk1_0)
    & ~ v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_12,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X15,X16] :
      ( ( ~ v3_tops_1(X16,X15)
        | v2_tops_1(k2_pre_topc(X15,X16),X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( ~ v2_tops_1(k2_pre_topc(X15,X16),X15)
        | v3_tops_1(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_1])])])])).

fof(c_0_15,plain,(
    ! [X9,X10] :
      ( ~ l1_pre_topc(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
      | m1_subset_1(k2_pre_topc(X9,X10),k1_zfmisc_1(u1_struct_0(X9))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_16,plain,(
    ! [X7,X8] :
      ( ~ r1_tarski(X7,X8)
      | X8 = k2_xboole_0(X7,k4_xboole_0(X8,X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X19,X20] :
      ( ( ~ v2_tops_1(X20,X19)
        | r1_tarski(X20,k2_tops_1(X19,X20))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) )
      & ( ~ r1_tarski(X20,k2_tops_1(X19,X20))
        | v2_tops_1(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_tops_1])])])])).

cnf(c_0_20,plain,
    ( v2_tops_1(k2_pre_topc(X2,X1),X2)
    | ~ v3_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(k2_xboole_0(X4,X5),X6)
      | r1_tarski(X4,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_23,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k2_tops_1(X2,X1))
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v2_tops_1(k2_pre_topc(esk1_0,X1),esk1_0)
    | ~ v3_tops_1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( v3_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_13])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( k2_xboole_0(esk2_0,k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0)) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(X1,k2_tops_1(esk1_0,X1))
    | ~ v2_tops_1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( v2_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_18])])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(k2_pre_topc(esk1_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

fof(c_0_36,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | r1_tarski(k2_tops_1(X17,k2_pre_topc(X17,X18)),k2_tops_1(X17,X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_tops_1])])])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk2_0,k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,plain,
    ( r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X2)),k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( k2_xboole_0(esk2_0,k4_xboole_0(k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),esk2_0)) = k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k2_tops_1(esk1_0,k2_pre_topc(esk1_0,X1)),k2_tops_1(esk1_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_13])).

fof(c_0_41,plain,(
    ! [X13,X14] :
      ( ( ~ v2_tops_1(X14,X13)
        | v1_tops_1(k3_subset_1(u1_struct_0(X13),X14),X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X13),X14),X13)
        | v2_tops_1(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_1])])])])).

cnf(c_0_42,plain,
    ( v2_tops_1(X1,X2)
    | ~ r1_tarski(X1,k2_tops_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),k2_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_18])).

cnf(c_0_45,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( v2_tops_1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,k2_tops_1(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_13])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),X1),esk1_0)
    | ~ v2_tops_1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_13])).

cnf(c_0_49,negated_conjecture,
    ( v2_tops_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_18])])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_18])]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.30  % Computer   : n010.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 12:36:14 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  # Version: 2.5pre002
% 0.10/0.30  # No SInE strategy applied
% 0.10/0.30  # Trying AutoSched0 for 299 seconds
% 0.15/0.34  # AutoSched0-Mode selected heuristic G_E___107_C00_02_nc_F1_PI_AE_Q4_CS_SP_PS_S00EN
% 0.15/0.34  # and selection function PSelectSmallestOrientable.
% 0.15/0.34  #
% 0.15/0.34  # Preprocessing time       : 0.027 s
% 0.15/0.34  # Presaturation interreduction done
% 0.15/0.34  
% 0.15/0.34  # Proof found!
% 0.15/0.34  # SZS status Theorem
% 0.15/0.34  # SZS output start CNFRefutation
% 0.15/0.34  fof(t91_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)=>v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_tops_1)).
% 0.15/0.34  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 0.15/0.34  fof(d5_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)<=>v2_tops_1(k2_pre_topc(X1,X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_1)).
% 0.15/0.34  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.15/0.34  fof(t45_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 0.15/0.34  fof(t88_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>r1_tarski(X2,k2_tops_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 0.15/0.34  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.15/0.34  fof(t72_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X2)),k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tops_1)).
% 0.15/0.34  fof(d4_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_1)).
% 0.15/0.34  fof(c_0_9, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)=>v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1))))), inference(assume_negation,[status(cth)],[t91_tops_1])).
% 0.15/0.34  fof(c_0_10, plain, ![X11, X12]:(~l1_pre_topc(X11)|(~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|r1_tarski(X12,k2_pre_topc(X11,X12)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 0.15/0.34  fof(c_0_11, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(v3_tops_1(esk2_0,esk1_0)&~v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.15/0.34  cnf(c_0_12, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.34  cnf(c_0_13, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.34  fof(c_0_14, plain, ![X15, X16]:((~v3_tops_1(X16,X15)|v2_tops_1(k2_pre_topc(X15,X16),X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))&(~v2_tops_1(k2_pre_topc(X15,X16),X15)|v3_tops_1(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_1])])])])).
% 0.15/0.34  fof(c_0_15, plain, ![X9, X10]:(~l1_pre_topc(X9)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|m1_subset_1(k2_pre_topc(X9,X10),k1_zfmisc_1(u1_struct_0(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.15/0.34  fof(c_0_16, plain, ![X7, X8]:(~r1_tarski(X7,X8)|X8=k2_xboole_0(X7,k4_xboole_0(X8,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).
% 0.15/0.34  cnf(c_0_17, negated_conjecture, (r1_tarski(X1,k2_pre_topc(esk1_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.15/0.34  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.34  fof(c_0_19, plain, ![X19, X20]:((~v2_tops_1(X20,X19)|r1_tarski(X20,k2_tops_1(X19,X20))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))&(~r1_tarski(X20,k2_tops_1(X19,X20))|v2_tops_1(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~l1_pre_topc(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_tops_1])])])])).
% 0.15/0.34  cnf(c_0_20, plain, (v2_tops_1(k2_pre_topc(X2,X1),X2)|~v3_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.34  cnf(c_0_21, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.34  fof(c_0_22, plain, ![X4, X5, X6]:(~r1_tarski(k2_xboole_0(X4,X5),X6)|r1_tarski(X4,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.15/0.34  cnf(c_0_23, plain, (X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.15/0.34  cnf(c_0_24, negated_conjecture, (r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.15/0.34  cnf(c_0_25, plain, (r1_tarski(X1,k2_tops_1(X2,X1))|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.15/0.34  cnf(c_0_26, negated_conjecture, (v2_tops_1(k2_pre_topc(esk1_0,X1),esk1_0)|~v3_tops_1(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_20, c_0_13])).
% 0.15/0.34  cnf(c_0_27, negated_conjecture, (v3_tops_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.34  cnf(c_0_28, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_21, c_0_13])).
% 0.15/0.34  cnf(c_0_29, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.15/0.34  cnf(c_0_30, negated_conjecture, (k2_xboole_0(esk2_0,k4_xboole_0(k2_pre_topc(esk1_0,esk2_0),esk2_0))=k2_pre_topc(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.15/0.34  cnf(c_0_31, negated_conjecture, (r1_tarski(X1,k2_tops_1(esk1_0,X1))|~v2_tops_1(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_25, c_0_13])).
% 0.15/0.34  cnf(c_0_32, negated_conjecture, (v2_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_18])])).
% 0.15/0.34  cnf(c_0_33, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_28, c_0_18])).
% 0.15/0.34  cnf(c_0_34, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(k2_pre_topc(esk1_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.15/0.34  cnf(c_0_35, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,esk2_0),k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.15/0.34  fof(c_0_36, plain, ![X17, X18]:(~l1_pre_topc(X17)|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|r1_tarski(k2_tops_1(X17,k2_pre_topc(X17,X18)),k2_tops_1(X17,X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_tops_1])])])).
% 0.15/0.34  cnf(c_0_37, negated_conjecture, (r1_tarski(esk2_0,k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.15/0.34  cnf(c_0_38, plain, (r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X2)),k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.15/0.34  cnf(c_0_39, negated_conjecture, (k2_xboole_0(esk2_0,k4_xboole_0(k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),esk2_0))=k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_23, c_0_37])).
% 0.15/0.34  cnf(c_0_40, negated_conjecture, (r1_tarski(k2_tops_1(esk1_0,k2_pre_topc(esk1_0,X1)),k2_tops_1(esk1_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_38, c_0_13])).
% 0.15/0.34  fof(c_0_41, plain, ![X13, X14]:((~v2_tops_1(X14,X13)|v1_tops_1(k3_subset_1(u1_struct_0(X13),X14),X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))&(~v1_tops_1(k3_subset_1(u1_struct_0(X13),X14),X13)|v2_tops_1(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_1])])])])).
% 0.15/0.34  cnf(c_0_42, plain, (v2_tops_1(X1,X2)|~r1_tarski(X1,k2_tops_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.15/0.34  cnf(c_0_43, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),X1)), inference(spm,[status(thm)],[c_0_29, c_0_39])).
% 0.15/0.34  cnf(c_0_44, negated_conjecture, (r1_tarski(k2_tops_1(esk1_0,k2_pre_topc(esk1_0,esk2_0)),k2_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_40, c_0_18])).
% 0.15/0.34  cnf(c_0_45, plain, (v1_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.15/0.34  cnf(c_0_46, negated_conjecture, (v2_tops_1(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,k2_tops_1(esk1_0,X1))), inference(spm,[status(thm)],[c_0_42, c_0_13])).
% 0.15/0.34  cnf(c_0_47, negated_conjecture, (r1_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.15/0.34  cnf(c_0_48, negated_conjecture, (v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),X1),esk1_0)|~v2_tops_1(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_45, c_0_13])).
% 0.15/0.34  cnf(c_0_49, negated_conjecture, (v2_tops_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_18])])).
% 0.15/0.34  cnf(c_0_50, negated_conjecture, (~v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.34  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_18])]), c_0_50]), ['proof']).
% 0.15/0.34  # SZS output end CNFRefutation
% 0.15/0.34  # Proof object total steps             : 52
% 0.15/0.34  # Proof object clause steps            : 33
% 0.15/0.34  # Proof object formula steps           : 19
% 0.15/0.34  # Proof object conjectures             : 27
% 0.15/0.34  # Proof object clause conjectures      : 24
% 0.15/0.34  # Proof object formula conjectures     : 3
% 0.15/0.34  # Proof object initial clauses used    : 13
% 0.15/0.34  # Proof object initial formulas used   : 9
% 0.15/0.34  # Proof object generating inferences   : 20
% 0.15/0.34  # Proof object simplifying inferences  : 9
% 0.15/0.34  # Training examples: 0 positive, 0 negative
% 0.15/0.34  # Parsed axioms                        : 9
% 0.15/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.34  # Initial clauses                      : 15
% 0.15/0.34  # Removed in clause preprocessing      : 0
% 0.15/0.34  # Initial clauses in saturation        : 15
% 0.15/0.34  # Processed clauses                    : 66
% 0.15/0.34  # ...of these trivial                  : 1
% 0.15/0.34  # ...subsumed                          : 1
% 0.15/0.34  # ...remaining for further processing  : 64
% 0.15/0.34  # Other redundant clauses eliminated   : 0
% 0.15/0.34  # Clauses deleted for lack of memory   : 0
% 0.15/0.34  # Backward-subsumed                    : 0
% 0.15/0.34  # Backward-rewritten                   : 0
% 0.15/0.34  # Generated clauses                    : 58
% 0.15/0.34  # ...of the previous two non-trivial   : 54
% 0.15/0.34  # Contextual simplify-reflections      : 0
% 0.15/0.34  # Paramodulations                      : 58
% 0.15/0.34  # Factorizations                       : 0
% 0.15/0.34  # Equation resolutions                 : 0
% 0.15/0.34  # Propositional unsat checks           : 0
% 0.15/0.34  #    Propositional check models        : 0
% 0.15/0.34  #    Propositional check unsatisfiable : 0
% 0.15/0.34  #    Propositional clauses             : 0
% 0.15/0.34  #    Propositional clauses after purity: 0
% 0.15/0.34  #    Propositional unsat core size     : 0
% 0.15/0.34  #    Propositional preprocessing time  : 0.000
% 0.15/0.34  #    Propositional encoding time       : 0.000
% 0.15/0.34  #    Propositional solver time         : 0.000
% 0.15/0.34  #    Success case prop preproc time    : 0.000
% 0.15/0.34  #    Success case prop encoding time   : 0.000
% 0.15/0.34  #    Success case prop solver time     : 0.000
% 0.15/0.34  # Current number of processed clauses  : 49
% 0.15/0.34  #    Positive orientable unit clauses  : 24
% 0.15/0.34  #    Positive unorientable unit clauses: 0
% 0.15/0.34  #    Negative unit clauses             : 1
% 0.15/0.34  #    Non-unit-clauses                  : 24
% 0.15/0.34  # Current number of unprocessed clauses: 18
% 0.15/0.34  # ...number of literals in the above   : 21
% 0.15/0.34  # Current number of archived formulas  : 0
% 0.15/0.34  # Current number of archived clauses   : 15
% 0.15/0.34  # Clause-clause subsumption calls (NU) : 116
% 0.15/0.34  # Rec. Clause-clause subsumption calls : 98
% 0.15/0.34  # Non-unit clause-clause subsumptions  : 0
% 0.15/0.34  # Unit Clause-clause subsumption calls : 10
% 0.15/0.34  # Rewrite failures with RHS unbound    : 0
% 0.15/0.34  # BW rewrite match attempts            : 8
% 0.15/0.34  # BW rewrite match successes           : 0
% 0.15/0.34  # Condensation attempts                : 0
% 0.15/0.34  # Condensation successes               : 0
% 0.15/0.34  # Termbank termtop insertions          : 2719
% 0.15/0.34  
% 0.15/0.34  # -------------------------------------------------
% 0.15/0.34  # User time                : 0.031 s
% 0.15/0.34  # System time              : 0.003 s
% 0.15/0.34  # Total time               : 0.034 s
% 0.15/0.34  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
