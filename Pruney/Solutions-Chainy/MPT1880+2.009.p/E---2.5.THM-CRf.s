%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:30 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 156 expanded)
%              Number of clauses        :   27 (  50 expanded)
%              Number of leaves         :    8 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :  192 ( 914 expanded)
%              Number of equality atoms :   23 (  37 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   31 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v1_tops_1(X2,X1)
              & v2_tex_2(X2,X1) )
           => v3_tex_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

fof(d2_tops_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t41_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r1_tarski(X3,X2)
                 => k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d7_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tex_2(X2,X1)
          <=> ( v2_tex_2(X2,X1)
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_tex_2(X3,X1)
                      & r1_tarski(X2,X3) )
                   => X2 = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ( v1_tops_1(X2,X1)
                & v2_tex_2(X2,X1) )
             => v3_tex_2(X2,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t48_tex_2])).

fof(c_0_9,plain,(
    ! [X13,X14] :
      ( ( ~ v1_tops_1(X14,X13)
        | k2_pre_topc(X13,X14) = u1_struct_0(X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( k2_pre_topc(X13,X14) != u1_struct_0(X13)
        | v1_tops_1(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & v1_tops_1(esk4_0,esk3_0)
    & v2_tex_2(esk4_0,esk3_0)
    & ~ v3_tex_2(esk4_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,X5)
      | k3_xboole_0(X4,X5) = X4 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_12,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X6))
      | k9_subset_1(X6,X7,X8) = k3_xboole_0(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_13,plain,(
    ! [X19,X20,X21] :
      ( ( ~ v2_tex_2(X20,X19)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ r1_tarski(X21,X20)
        | k9_subset_1(u1_struct_0(X19),X20,k2_pre_topc(X19,X21)) = X21
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk2_2(X19,X20),k1_zfmisc_1(u1_struct_0(X19)))
        | v2_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r1_tarski(esk2_2(X19,X20),X20)
        | v2_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( k9_subset_1(u1_struct_0(X19),X20,k2_pre_topc(X19,esk2_2(X19,X20))) != esk2_2(X19,X20)
        | v2_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_tex_2])])])])])])).

cnf(c_0_14,plain,
    ( k2_pre_topc(X2,X1) = u1_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v1_tops_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_18,plain,(
    ! [X11,X12] :
      ( ~ l1_pre_topc(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
      | m1_subset_1(k2_pre_topc(X11,X12),k1_zfmisc_1(u1_struct_0(X11))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k9_subset_1(u1_struct_0(X2),X1,k2_pre_topc(X2,X3)) = X3
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( k2_pre_topc(esk3_0,esk4_0) = u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_27,plain,(
    ! [X15,X16,X17] :
      ( ( v2_tex_2(X16,X15)
        | ~ v3_tex_2(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ v2_tex_2(X17,X15)
        | ~ r1_tarski(X16,X17)
        | X16 = X17
        | ~ v3_tex_2(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk1_2(X15,X16),k1_zfmisc_1(u1_struct_0(X15)))
        | ~ v2_tex_2(X16,X15)
        | v3_tex_2(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( v2_tex_2(esk1_2(X15,X16),X15)
        | ~ v2_tex_2(X16,X15)
        | v3_tex_2(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( r1_tarski(X16,esk1_2(X15,X16))
        | ~ v2_tex_2(X16,X15)
        | v3_tex_2(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( X16 != esk1_2(X15,X16)
        | ~ v2_tex_2(X16,X15)
        | v3_tex_2(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).

cnf(c_0_28,plain,
    ( k9_subset_1(X1,X2,X3) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk3_0),X1,u1_struct_0(esk3_0)) = esk4_0
    | ~ v2_tex_2(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_22]),c_0_23]),c_0_16])]),c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_22]),c_0_16]),c_0_17])])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,esk1_2(X2,X1))
    | v3_tex_2(X1,X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( v2_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,negated_conjecture,
    ( ~ v3_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,plain,
    ( v2_tex_2(esk1_2(X1,X2),X1)
    | v3_tex_2(X2,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v3_tex_2(X2,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( esk4_0 = X1
    | ~ v2_tex_2(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk4_0,esk1_2(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_17]),c_0_33]),c_0_16])]),c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( v2_tex_2(esk1_2(esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_17]),c_0_33]),c_0_16])]),c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk1_2(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_17]),c_0_33]),c_0_16])]),c_0_34])).

cnf(c_0_41,plain,
    ( v3_tex_2(X1,X2)
    | X1 != esk1_2(X2,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( esk1_2(esk3_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_33]),c_0_16]),c_0_17])]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:36:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.029 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t48_tex_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v1_tops_1(X2,X1)&v2_tex_2(X2,X1))=>v3_tex_2(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 0.14/0.38  fof(d2_tops_3, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 0.14/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.14/0.38  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.14/0.38  fof(t41_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X3,X2)=>k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3))=X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 0.14/0.38  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.14/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.14/0.38  fof(d7_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>(v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X3,X1)&r1_tarski(X2,X3))=>X2=X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 0.14/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v1_tops_1(X2,X1)&v2_tex_2(X2,X1))=>v3_tex_2(X2,X1))))), inference(assume_negation,[status(cth)],[t48_tex_2])).
% 0.14/0.38  fof(c_0_9, plain, ![X13, X14]:((~v1_tops_1(X14,X13)|k2_pre_topc(X13,X14)=u1_struct_0(X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))&(k2_pre_topc(X13,X14)!=u1_struct_0(X13)|v1_tops_1(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|~l1_pre_topc(X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).
% 0.14/0.38  fof(c_0_10, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((v1_tops_1(esk4_0,esk3_0)&v2_tex_2(esk4_0,esk3_0))&~v3_tex_2(esk4_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.14/0.38  fof(c_0_11, plain, ![X4, X5]:(~r1_tarski(X4,X5)|k3_xboole_0(X4,X5)=X4), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.14/0.38  fof(c_0_12, plain, ![X6, X7, X8]:(~m1_subset_1(X8,k1_zfmisc_1(X6))|k9_subset_1(X6,X7,X8)=k3_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.14/0.38  fof(c_0_13, plain, ![X19, X20, X21]:((~v2_tex_2(X20,X19)|(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X19)))|(~r1_tarski(X21,X20)|k9_subset_1(u1_struct_0(X19),X20,k2_pre_topc(X19,X21))=X21))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&((m1_subset_1(esk2_2(X19,X20),k1_zfmisc_1(u1_struct_0(X19)))|v2_tex_2(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&((r1_tarski(esk2_2(X19,X20),X20)|v2_tex_2(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&(k9_subset_1(u1_struct_0(X19),X20,k2_pre_topc(X19,esk2_2(X19,X20)))!=esk2_2(X19,X20)|v2_tex_2(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t41_tex_2])])])])])])).
% 0.14/0.38  cnf(c_0_14, plain, (k2_pre_topc(X2,X1)=u1_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_15, negated_conjecture, (v1_tops_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  fof(c_0_18, plain, ![X11, X12]:(~l1_pre_topc(X11)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|m1_subset_1(k2_pre_topc(X11,X12),k1_zfmisc_1(u1_struct_0(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.14/0.38  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_20, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_21, plain, (k9_subset_1(u1_struct_0(X2),X1,k2_pre_topc(X2,X3))=X3|v2_struct_0(X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (k2_pre_topc(esk3_0,esk4_0)=u1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_25, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  fof(c_0_26, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.14/0.38  fof(c_0_27, plain, ![X15, X16, X17]:(((v2_tex_2(X16,X15)|~v3_tex_2(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))&(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))|(~v2_tex_2(X17,X15)|~r1_tarski(X16,X17)|X16=X17)|~v3_tex_2(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15)))&((m1_subset_1(esk1_2(X15,X16),k1_zfmisc_1(u1_struct_0(X15)))|~v2_tex_2(X16,X15)|v3_tex_2(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))&(((v2_tex_2(esk1_2(X15,X16),X15)|~v2_tex_2(X16,X15)|v3_tex_2(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))&(r1_tarski(X16,esk1_2(X15,X16))|~v2_tex_2(X16,X15)|v3_tex_2(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15)))&(X16!=esk1_2(X15,X16)|~v2_tex_2(X16,X15)|v3_tex_2(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).
% 0.14/0.38  cnf(c_0_28, plain, (k9_subset_1(X1,X2,X3)=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (k9_subset_1(u1_struct_0(esk3_0),X1,u1_struct_0(esk3_0))=esk4_0|~v2_tex_2(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(esk4_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_17]), c_0_22]), c_0_23]), c_0_16])]), c_0_24])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_22]), c_0_16]), c_0_17])])).
% 0.14/0.38  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.38  cnf(c_0_32, plain, (r1_tarski(X1,esk1_2(X2,X1))|v3_tex_2(X1,X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (v2_tex_2(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_34, negated_conjecture, (~v3_tex_2(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_35, plain, (v2_tex_2(esk1_2(X1,X2),X1)|v3_tex_2(X2,X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.38  cnf(c_0_36, plain, (m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v3_tex_2(X2,X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (esk4_0=X1|~v2_tex_2(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(esk4_0,X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])]), c_0_31])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (r1_tarski(esk4_0,esk1_2(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_17]), c_0_33]), c_0_16])]), c_0_34])).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (v2_tex_2(esk1_2(esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_17]), c_0_33]), c_0_16])]), c_0_34])).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk1_2(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_17]), c_0_33]), c_0_16])]), c_0_34])).
% 0.14/0.38  cnf(c_0_41, plain, (v3_tex_2(X1,X2)|X1!=esk1_2(X2,X1)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, (esk1_2(esk3_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40])])).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_33]), c_0_16]), c_0_17])]), c_0_34]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 44
% 0.14/0.38  # Proof object clause steps            : 27
% 0.14/0.38  # Proof object formula steps           : 17
% 0.14/0.38  # Proof object conjectures             : 19
% 0.14/0.38  # Proof object clause conjectures      : 16
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 17
% 0.14/0.38  # Proof object initial formulas used   : 8
% 0.14/0.38  # Proof object generating inferences   : 10
% 0.14/0.38  # Proof object simplifying inferences  : 34
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 8
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 24
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 24
% 0.14/0.38  # Processed clauses                    : 76
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 3
% 0.14/0.38  # ...remaining for further processing  : 73
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 10
% 0.14/0.38  # Generated clauses                    : 69
% 0.14/0.38  # ...of the previous two non-trivial   : 67
% 0.14/0.38  # Contextual simplify-reflections      : 1
% 0.14/0.38  # Paramodulations                      : 69
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 39
% 0.14/0.38  #    Positive orientable unit clauses  : 8
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 2
% 0.14/0.38  #    Non-unit-clauses                  : 29
% 0.14/0.38  # Current number of unprocessed clauses: 33
% 0.14/0.38  # ...number of literals in the above   : 163
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 34
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 822
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 199
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.14/0.38  # Unit Clause-clause subsumption calls : 14
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 1
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 4229
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.034 s
% 0.14/0.38  # System time              : 0.004 s
% 0.14/0.38  # Total time               : 0.038 s
% 0.14/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
