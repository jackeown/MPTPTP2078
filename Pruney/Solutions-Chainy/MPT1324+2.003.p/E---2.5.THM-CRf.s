%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:25 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   30 (  63 expanded)
%              Number of clauses        :   19 (  25 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :  100 ( 251 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t14_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2)
        & ! [X4] :
            ( ( r1_tarski(X1,X4)
              & r1_tarski(X3,X4) )
           => r1_tarski(X2,X4) ) )
     => X2 = k2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(t44_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X3)),k5_setfam_1(u1_struct_0(X1),X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_2)).

fof(t45_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X3)))
               => r1_tarski(X2,k5_setfam_1(u1_struct_0(X1),X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_tops_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(c_0_5,plain,(
    ! [X10,X11,X12] :
      ( ( r1_tarski(X10,esk1_3(X10,X11,X12))
        | ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X12,X11)
        | X11 = k2_xboole_0(X10,X12) )
      & ( r1_tarski(X12,esk1_3(X10,X11,X12))
        | ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X12,X11)
        | X11 = k2_xboole_0(X10,X12) )
      & ( ~ r1_tarski(X11,esk1_3(X10,X11,X12))
        | ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X12,X11)
        | X11 = k2_xboole_0(X10,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).

fof(c_0_6,plain,(
    ! [X14,X15,X16] :
      ( ~ l1_pre_topc(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
      | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
      | r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X14,X15)),k1_tops_2(X14,X15,X16)),k5_setfam_1(u1_struct_0(X14),X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_2])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ( r1_tarski(X2,k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X3)))
                 => r1_tarski(X2,k5_setfam_1(u1_struct_0(X1),X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t45_tops_2])).

cnf(c_0_8,plain,
    ( r1_tarski(X1,esk1_3(X1,X2,X3))
    | X2 = k2_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X3)),k5_setfam_1(u1_struct_0(X1),X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    & r1_tarski(esk3_0,k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0)))
    & ~ r1_tarski(esk3_0,k5_setfam_1(u1_struct_0(esk2_0),esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_11,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_12,plain,
    ( k2_xboole_0(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X2,X3)),k1_tops_2(X2,X3,X4))) = k5_setfam_1(u1_struct_0(X2),X4)
    | r1_tarski(X1,esk1_3(X1,k5_setfam_1(u1_struct_0(X2),X4),k5_setfam_1(u1_struct_0(k1_pre_topc(X2,X3)),k1_tops_2(X2,X3,X4))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(X2),X4)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( k2_xboole_0(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,X2)),k1_tops_2(esk2_0,X2,esk4_0))) = k5_setfam_1(u1_struct_0(esk2_0),esk4_0)
    | r1_tarski(X1,esk1_3(X1,k5_setfam_1(u1_struct_0(esk2_0),esk4_0),k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,X2)),k1_tops_2(esk2_0,X2,esk4_0))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(esk2_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( k2_xboole_0(k5_setfam_1(u1_struct_0(esk2_0),esk4_0),k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,X1)),k1_tops_2(esk2_0,X1,esk4_0))) = k5_setfam_1(u1_struct_0(esk2_0),esk4_0)
    | r1_tarski(k5_setfam_1(u1_struct_0(esk2_0),esk4_0),esk1_3(k5_setfam_1(u1_struct_0(esk2_0),esk4_0),k5_setfam_1(u1_struct_0(esk2_0),esk4_0),k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,X1)),k1_tops_2(esk2_0,X1,esk4_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_20,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | r1_tarski(X7,k2_xboole_0(X9,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_21,plain,
    ( X1 = k2_xboole_0(X2,X3)
    | ~ r1_tarski(X1,esk1_3(X2,X1,X3))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,negated_conjecture,
    ( k2_xboole_0(k5_setfam_1(u1_struct_0(esk2_0),esk4_0),k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0))) = k5_setfam_1(u1_struct_0(esk2_0),esk4_0)
    | r1_tarski(k5_setfam_1(u1_struct_0(esk2_0),esk4_0),esk1_3(k5_setfam_1(u1_struct_0(esk2_0),esk4_0),k5_setfam_1(u1_struct_0(esk2_0),esk4_0),k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( k2_xboole_0(k5_setfam_1(u1_struct_0(esk2_0),esk4_0),k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0))) = k5_setfam_1(u1_struct_0(esk2_0),esk4_0)
    | ~ r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0)),k5_setfam_1(u1_struct_0(esk2_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_17])])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(X1,k5_setfam_1(u1_struct_0(esk2_0),esk4_0))
    | ~ r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0)),k5_setfam_1(u1_struct_0(esk2_0),esk4_0))
    | ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(X1,k5_setfam_1(u1_struct_0(esk2_0),esk4_0))
    | ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_9]),c_0_13]),c_0_19]),c_0_14])])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk3_0,k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k5_setfam_1(u1_struct_0(esk2_0),esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.43  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.43  #
% 0.19/0.43  # Preprocessing time       : 0.027 s
% 0.19/0.43  # Presaturation interreduction done
% 0.19/0.43  
% 0.19/0.43  # Proof found!
% 0.19/0.43  # SZS status Theorem
% 0.19/0.43  # SZS output start CNFRefutation
% 0.19/0.43  fof(t14_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X3,X2))&![X4]:((r1_tarski(X1,X4)&r1_tarski(X3,X4))=>r1_tarski(X2,X4)))=>X2=k2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 0.19/0.43  fof(t44_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X3)),k5_setfam_1(u1_struct_0(X1),X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_2)).
% 0.19/0.43  fof(t45_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X3)))=>r1_tarski(X2,k5_setfam_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_tops_2)).
% 0.19/0.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.43  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.19/0.43  fof(c_0_5, plain, ![X10, X11, X12]:(((r1_tarski(X10,esk1_3(X10,X11,X12))|(~r1_tarski(X10,X11)|~r1_tarski(X12,X11))|X11=k2_xboole_0(X10,X12))&(r1_tarski(X12,esk1_3(X10,X11,X12))|(~r1_tarski(X10,X11)|~r1_tarski(X12,X11))|X11=k2_xboole_0(X10,X12)))&(~r1_tarski(X11,esk1_3(X10,X11,X12))|(~r1_tarski(X10,X11)|~r1_tarski(X12,X11))|X11=k2_xboole_0(X10,X12))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).
% 0.19/0.43  fof(c_0_6, plain, ![X14, X15, X16]:(~l1_pre_topc(X14)|(~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|(~m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))|r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X14,X15)),k1_tops_2(X14,X15,X16)),k5_setfam_1(u1_struct_0(X14),X16))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_2])])])).
% 0.19/0.43  fof(c_0_7, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X3)))=>r1_tarski(X2,k5_setfam_1(u1_struct_0(X1),X3))))))), inference(assume_negation,[status(cth)],[t45_tops_2])).
% 0.19/0.43  cnf(c_0_8, plain, (r1_tarski(X1,esk1_3(X1,X2,X3))|X2=k2_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.43  cnf(c_0_9, plain, (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X3)),k5_setfam_1(u1_struct_0(X1),X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.43  fof(c_0_10, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))&(r1_tarski(esk3_0,k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0)))&~r1_tarski(esk3_0,k5_setfam_1(u1_struct_0(esk2_0),esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.19/0.43  fof(c_0_11, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.43  cnf(c_0_12, plain, (k2_xboole_0(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X2,X3)),k1_tops_2(X2,X3,X4)))=k5_setfam_1(u1_struct_0(X2),X4)|r1_tarski(X1,esk1_3(X1,k5_setfam_1(u1_struct_0(X2),X4),k5_setfam_1(u1_struct_0(k1_pre_topc(X2,X3)),k1_tops_2(X2,X3,X4))))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)|~r1_tarski(X1,k5_setfam_1(u1_struct_0(X2),X4))), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.19/0.43  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.43  cnf(c_0_14, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.43  cnf(c_0_15, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.43  cnf(c_0_16, negated_conjecture, (k2_xboole_0(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,X2)),k1_tops_2(esk2_0,X2,esk4_0)))=k5_setfam_1(u1_struct_0(esk2_0),esk4_0)|r1_tarski(X1,esk1_3(X1,k5_setfam_1(u1_struct_0(esk2_0),esk4_0),k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,X2)),k1_tops_2(esk2_0,X2,esk4_0))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,k5_setfam_1(u1_struct_0(esk2_0),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])])).
% 0.19/0.43  cnf(c_0_17, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_15])).
% 0.19/0.43  cnf(c_0_18, negated_conjecture, (k2_xboole_0(k5_setfam_1(u1_struct_0(esk2_0),esk4_0),k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,X1)),k1_tops_2(esk2_0,X1,esk4_0)))=k5_setfam_1(u1_struct_0(esk2_0),esk4_0)|r1_tarski(k5_setfam_1(u1_struct_0(esk2_0),esk4_0),esk1_3(k5_setfam_1(u1_struct_0(esk2_0),esk4_0),k5_setfam_1(u1_struct_0(esk2_0),esk4_0),k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,X1)),k1_tops_2(esk2_0,X1,esk4_0))))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.43  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.43  fof(c_0_20, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|r1_tarski(X7,k2_xboole_0(X9,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.19/0.43  cnf(c_0_21, plain, (X1=k2_xboole_0(X2,X3)|~r1_tarski(X1,esk1_3(X2,X1,X3))|~r1_tarski(X2,X1)|~r1_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.43  cnf(c_0_22, negated_conjecture, (k2_xboole_0(k5_setfam_1(u1_struct_0(esk2_0),esk4_0),k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0)))=k5_setfam_1(u1_struct_0(esk2_0),esk4_0)|r1_tarski(k5_setfam_1(u1_struct_0(esk2_0),esk4_0),esk1_3(k5_setfam_1(u1_struct_0(esk2_0),esk4_0),k5_setfam_1(u1_struct_0(esk2_0),esk4_0),k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0))))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.43  cnf(c_0_23, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.43  cnf(c_0_24, negated_conjecture, (k2_xboole_0(k5_setfam_1(u1_struct_0(esk2_0),esk4_0),k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0)))=k5_setfam_1(u1_struct_0(esk2_0),esk4_0)|~r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0)),k5_setfam_1(u1_struct_0(esk2_0),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_17])])).
% 0.19/0.43  cnf(c_0_25, negated_conjecture, (r1_tarski(X1,k5_setfam_1(u1_struct_0(esk2_0),esk4_0))|~r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0)),k5_setfam_1(u1_struct_0(esk2_0),esk4_0))|~r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.43  cnf(c_0_26, negated_conjecture, (r1_tarski(X1,k5_setfam_1(u1_struct_0(esk2_0),esk4_0))|~r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_9]), c_0_13]), c_0_19]), c_0_14])])).
% 0.19/0.43  cnf(c_0_27, negated_conjecture, (r1_tarski(esk3_0,k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.43  cnf(c_0_28, negated_conjecture, (~r1_tarski(esk3_0,k5_setfam_1(u1_struct_0(esk2_0),esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.43  cnf(c_0_29, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), ['proof']).
% 0.19/0.43  # SZS output end CNFRefutation
% 0.19/0.43  # Proof object total steps             : 30
% 0.19/0.43  # Proof object clause steps            : 19
% 0.19/0.43  # Proof object formula steps           : 11
% 0.19/0.43  # Proof object conjectures             : 15
% 0.19/0.43  # Proof object clause conjectures      : 12
% 0.19/0.43  # Proof object formula conjectures     : 3
% 0.19/0.43  # Proof object initial clauses used    : 10
% 0.19/0.43  # Proof object initial formulas used   : 5
% 0.19/0.43  # Proof object generating inferences   : 8
% 0.19/0.43  # Proof object simplifying inferences  : 10
% 0.19/0.43  # Training examples: 0 positive, 0 negative
% 0.19/0.43  # Parsed axioms                        : 5
% 0.19/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.43  # Initial clauses                      : 13
% 0.19/0.43  # Removed in clause preprocessing      : 0
% 0.19/0.43  # Initial clauses in saturation        : 13
% 0.19/0.43  # Processed clauses                    : 444
% 0.19/0.43  # ...of these trivial                  : 1
% 0.19/0.43  # ...subsumed                          : 259
% 0.19/0.43  # ...remaining for further processing  : 184
% 0.19/0.43  # Other redundant clauses eliminated   : 2
% 0.19/0.43  # Clauses deleted for lack of memory   : 0
% 0.19/0.43  # Backward-subsumed                    : 2
% 0.19/0.43  # Backward-rewritten                   : 7
% 0.19/0.43  # Generated clauses                    : 1848
% 0.19/0.43  # ...of the previous two non-trivial   : 1584
% 0.19/0.43  # Contextual simplify-reflections      : 0
% 0.19/0.43  # Paramodulations                      : 1846
% 0.19/0.43  # Factorizations                       : 0
% 0.19/0.43  # Equation resolutions                 : 2
% 0.19/0.43  # Propositional unsat checks           : 0
% 0.19/0.43  #    Propositional check models        : 0
% 0.19/0.43  #    Propositional check unsatisfiable : 0
% 0.19/0.43  #    Propositional clauses             : 0
% 0.19/0.43  #    Propositional clauses after purity: 0
% 0.19/0.43  #    Propositional unsat core size     : 0
% 0.19/0.43  #    Propositional preprocessing time  : 0.000
% 0.19/0.43  #    Propositional encoding time       : 0.000
% 0.19/0.43  #    Propositional solver time         : 0.000
% 0.19/0.43  #    Success case prop preproc time    : 0.000
% 0.19/0.43  #    Success case prop encoding time   : 0.000
% 0.19/0.43  #    Success case prop solver time     : 0.000
% 0.19/0.43  # Current number of processed clauses  : 161
% 0.19/0.43  #    Positive orientable unit clauses  : 8
% 0.19/0.43  #    Positive unorientable unit clauses: 0
% 0.19/0.43  #    Negative unit clauses             : 2
% 0.19/0.43  #    Non-unit-clauses                  : 151
% 0.19/0.43  # Current number of unprocessed clauses: 1137
% 0.19/0.43  # ...number of literals in the above   : 4018
% 0.19/0.43  # Current number of archived formulas  : 0
% 0.19/0.43  # Current number of archived clauses   : 21
% 0.19/0.43  # Clause-clause subsumption calls (NU) : 5267
% 0.19/0.43  # Rec. Clause-clause subsumption calls : 3964
% 0.19/0.43  # Non-unit clause-clause subsumptions  : 216
% 0.19/0.43  # Unit Clause-clause subsumption calls : 26
% 0.19/0.43  # Rewrite failures with RHS unbound    : 0
% 0.19/0.43  # BW rewrite match attempts            : 10
% 0.19/0.43  # BW rewrite match successes           : 3
% 0.19/0.43  # Condensation attempts                : 0
% 0.19/0.43  # Condensation successes               : 0
% 0.19/0.43  # Termbank termtop insertions          : 86802
% 0.19/0.43  
% 0.19/0.43  # -------------------------------------------------
% 0.19/0.43  # User time                : 0.081 s
% 0.19/0.43  # System time              : 0.009 s
% 0.19/0.43  # Total time               : 0.090 s
% 0.19/0.43  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
