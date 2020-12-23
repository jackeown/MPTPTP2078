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
% DateTime   : Thu Dec  3 11:10:35 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   31 (  61 expanded)
%              Number of clauses        :   20 (  23 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :  127 ( 287 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v4_pre_topc(X2,X1)
                  & r1_tarski(X3,X2) )
               => r1_tarski(k2_pre_topc(X1,X3),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t45_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( r2_hidden(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k2_pre_topc(X1,X2))
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v4_pre_topc(X4,X1)
                        & r1_tarski(X2,X4) )
                     => r2_hidden(X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_pre_topc)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v4_pre_topc(X2,X1)
                    & r1_tarski(X3,X2) )
                 => r1_tarski(k2_pre_topc(X1,X3),X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_tops_1])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_7,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_8,plain,(
    ! [X13,X14] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
      | m1_subset_1(k2_pre_topc(X13,X14),k1_zfmisc_1(u1_struct_0(X13))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_9,plain,(
    ! [X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X17,k2_pre_topc(X15,X16))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ v4_pre_topc(X18,X15)
        | ~ r1_tarski(X16,X18)
        | r2_hidden(X17,X18)
        | ~ r2_hidden(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk2_3(X15,X16,X17),k1_zfmisc_1(u1_struct_0(X15)))
        | r2_hidden(X17,k2_pre_topc(X15,X16))
        | ~ r2_hidden(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( v4_pre_topc(esk2_3(X15,X16,X17),X15)
        | r2_hidden(X17,k2_pre_topc(X15,X16))
        | ~ r2_hidden(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( r1_tarski(X16,esk2_3(X15,X16,X17))
        | r2_hidden(X17,k2_pre_topc(X15,X16))
        | ~ r2_hidden(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( ~ r2_hidden(X17,esk2_3(X15,X16,X17))
        | r2_hidden(X17,k2_pre_topc(X15,X16))
        | ~ r2_hidden(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_pre_topc])])])])])).

fof(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & v4_pre_topc(esk4_0,esk3_0)
    & r1_tarski(esk5_0,esk4_0)
    & ~ r1_tarski(k2_pre_topc(esk3_0,esk5_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,k2_pre_topc(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_pre_topc(X4,X2)
    | ~ r1_tarski(X3,X4)
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( v4_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_20,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,k2_pre_topc(esk3_0,X2))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(X2,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_2(k2_pre_topc(X1,X2),X3),u1_struct_0(X1))
    | r1_tarski(k2_pre_topc(X1,X2),X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk1_2(k2_pre_topc(esk3_0,X1),X2),esk4_0)
    | r1_tarski(k2_pre_topc(esk3_0,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk1_2(k2_pre_topc(esk3_0,X1),X2),u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk5_0),X1),u1_struct_0(esk3_0))
    | r1_tarski(k2_pre_topc(esk3_0,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_18])])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk5_0),X1),esk4_0)
    | r1_tarski(k2_pre_topc(esk3_0,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_23]),c_0_26])])).

cnf(c_0_29,negated_conjecture,
    ( ~ r1_tarski(k2_pre_topc(esk3_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:55:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t31_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)&r1_tarski(X3,X2))=>r1_tarski(k2_pre_topc(X1,X3),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_1)).
% 0.13/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.38  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.13/0.38  fof(t45_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(r2_hidden(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X4,X1)&r1_tarski(X2,X4))=>r2_hidden(X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_pre_topc)).
% 0.13/0.38  fof(c_0_5, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)&r1_tarski(X3,X2))=>r1_tarski(k2_pre_topc(X1,X3),X2)))))), inference(assume_negation,[status(cth)],[t31_tops_1])).
% 0.13/0.38  fof(c_0_6, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.38  fof(c_0_7, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.38  fof(c_0_8, plain, ![X13, X14]:(~l1_pre_topc(X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|m1_subset_1(k2_pre_topc(X13,X14),k1_zfmisc_1(u1_struct_0(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.13/0.38  fof(c_0_9, plain, ![X15, X16, X17, X18]:((~r2_hidden(X17,k2_pre_topc(X15,X16))|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X15)))|(~v4_pre_topc(X18,X15)|~r1_tarski(X16,X18)|r2_hidden(X17,X18)))|~r2_hidden(X17,u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))&((m1_subset_1(esk2_3(X15,X16,X17),k1_zfmisc_1(u1_struct_0(X15)))|r2_hidden(X17,k2_pre_topc(X15,X16))|~r2_hidden(X17,u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))&(((v4_pre_topc(esk2_3(X15,X16,X17),X15)|r2_hidden(X17,k2_pre_topc(X15,X16))|~r2_hidden(X17,u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))&(r1_tarski(X16,esk2_3(X15,X16,X17))|r2_hidden(X17,k2_pre_topc(X15,X16))|~r2_hidden(X17,u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15)))&(~r2_hidden(X17,esk2_3(X15,X16,X17))|r2_hidden(X17,k2_pre_topc(X15,X16))|~r2_hidden(X17,u1_struct_0(X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_pre_topc])])])])])).
% 0.13/0.38  fof(c_0_10, negated_conjecture, (l1_pre_topc(esk3_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((v4_pre_topc(esk4_0,esk3_0)&r1_tarski(esk5_0,esk4_0))&~r1_tarski(k2_pre_topc(esk3_0,esk5_0),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.13/0.38  cnf(c_0_11, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_12, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_13, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_14, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_15, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,k2_pre_topc(X2,X3))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~v4_pre_topc(X4,X2)|~r1_tarski(X3,X4)|~r2_hidden(X1,u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (v4_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_19, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.38  cnf(c_0_20, plain, (r1_tarski(k2_pre_topc(X1,X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (r2_hidden(X1,esk4_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,k2_pre_topc(esk3_0,X2))|~r2_hidden(X1,u1_struct_0(esk3_0))|~r1_tarski(X2,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])])).
% 0.13/0.38  cnf(c_0_22, plain, (r2_hidden(esk1_2(k2_pre_topc(X1,X2),X3),u1_struct_0(X1))|r1_tarski(k2_pre_topc(X1,X2),X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(esk1_2(k2_pre_topc(esk3_0,X1),X2),esk4_0)|r1_tarski(k2_pre_topc(esk3_0,X1),X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(esk1_2(k2_pre_topc(esk3_0,X1),X2),u1_struct_0(esk3_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_12])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk5_0),X1),u1_struct_0(esk3_0))|r1_tarski(k2_pre_topc(esk3_0,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_18])])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(esk1_2(k2_pre_topc(esk3_0,esk5_0),X1),esk4_0)|r1_tarski(k2_pre_topc(esk3_0,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_23]), c_0_26])])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (~r1_tarski(k2_pre_topc(esk3_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 31
% 0.13/0.38  # Proof object clause steps            : 20
% 0.13/0.38  # Proof object formula steps           : 11
% 0.13/0.38  # Proof object conjectures             : 14
% 0.13/0.38  # Proof object clause conjectures      : 11
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 12
% 0.13/0.38  # Proof object initial formulas used   : 5
% 0.13/0.38  # Proof object generating inferences   : 8
% 0.13/0.38  # Proof object simplifying inferences  : 9
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 5
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 17
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 17
% 0.13/0.38  # Processed clauses                    : 139
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 25
% 0.13/0.38  # ...remaining for further processing  : 114
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 290
% 0.13/0.38  # ...of the previous two non-trivial   : 285
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 290
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 97
% 0.13/0.38  #    Positive orientable unit clauses  : 14
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 82
% 0.13/0.38  # Current number of unprocessed clauses: 179
% 0.13/0.38  # ...number of literals in the above   : 626
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 17
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1039
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 567
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 25
% 0.13/0.38  # Unit Clause-clause subsumption calls : 19
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 10
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 10021
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.039 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.043 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
