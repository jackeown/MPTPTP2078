%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:11 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 151 expanded)
%              Number of clauses        :   24 (  57 expanded)
%              Number of leaves         :    6 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  142 ( 513 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(t7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                 => r2_hidden(X4,X3) ) )
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_pre_topc)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t48_pre_topc])).

fof(c_0_7,plain,(
    ! [X8,X9,X10] :
      ( ( m1_subset_1(esk1_3(X8,X9,X10),X8)
        | r1_tarski(X9,X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) )
      & ( r2_hidden(esk1_3(X8,X9,X10),X9)
        | r1_tarski(X9,X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) )
      & ( ~ r2_hidden(esk1_3(X8,X9,X10),X10)
        | r1_tarski(X9,X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

fof(c_0_8,plain,(
    ! [X14,X15] :
      ( ~ l1_pre_topc(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
      | m1_subset_1(k2_pre_topc(X14,X15),k1_zfmisc_1(u1_struct_0(X14))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_9,plain,(
    ! [X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X18,k2_pre_topc(X16,X17))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ v4_pre_topc(X19,X16)
        | ~ r1_tarski(X17,X19)
        | r2_hidden(X18,X19)
        | ~ r2_hidden(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk2_3(X16,X17,X18),k1_zfmisc_1(u1_struct_0(X16)))
        | r2_hidden(X18,k2_pre_topc(X16,X17))
        | ~ r2_hidden(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) )
      & ( v4_pre_topc(esk2_3(X16,X17,X18),X16)
        | r2_hidden(X18,k2_pre_topc(X16,X17))
        | ~ r2_hidden(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) )
      & ( r1_tarski(X17,esk2_3(X16,X17,X18))
        | r2_hidden(X18,k2_pre_topc(X16,X17))
        | ~ r2_hidden(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) )
      & ( ~ r2_hidden(X18,esk2_3(X16,X17,X18))
        | r2_hidden(X18,k2_pre_topc(X16,X17))
        | ~ r2_hidden(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_pre_topc])])])])])).

fof(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ~ r1_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_11,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | ~ r2_hidden(X7,X6)
      | r2_hidden(X7,X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_12,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,esk2_3(X2,X1,X3))
    | r2_hidden(X3,k2_pre_topc(X2,X1))
    | ~ r2_hidden(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,X3))
    | r2_hidden(esk1_3(u1_struct_0(X2),X1,k2_pre_topc(X2,X3)),X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_3(esk3_0,esk4_0,X1))
    | r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk4_0,k2_pre_topc(esk3_0,X1))
    | r2_hidden(esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,X1)),esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_15]),c_0_16])])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_23,plain,(
    ! [X12,X13] :
      ( ( ~ m1_subset_1(X12,k1_zfmisc_1(X13))
        | r1_tarski(X12,X13) )
      & ( ~ r1_tarski(X12,X13)
        | m1_subset_1(X12,k1_zfmisc_1(X13)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_3(esk3_0,esk4_0,X1))
    | r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0)),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_15]),c_0_22])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_3(esk3_0,esk4_0,esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0))))
    | r2_hidden(esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0)),k2_pre_topc(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0)),k2_pre_topc(esk3_0,esk4_0))
    | m1_subset_1(esk4_0,k1_zfmisc_1(esk2_3(esk3_0,esk4_0,esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0))))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,esk2_3(esk3_0,esk4_0,esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0))))
    | r2_hidden(esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0)),k2_pre_topc(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_28])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k2_pre_topc(X2,X3))
    | ~ r2_hidden(X1,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0)),esk2_3(esk3_0,esk4_0,esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0))))
    | r2_hidden(esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0)),k2_pre_topc(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_25])).

cnf(c_0_32,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0)),k2_pre_topc(esk3_0,esk4_0))
    | ~ r2_hidden(esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0)),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_16]),c_0_15])])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_hidden(esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0)),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_15])]),c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( ~ m1_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_20]),c_0_25])])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_13]),c_0_16]),c_0_15])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:24:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t48_pre_topc, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 0.19/0.37  fof(t7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 0.19/0.37  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.19/0.37  fof(t45_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(r2_hidden(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X4,X1)&r1_tarski(X2,X4))=>r2_hidden(X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_pre_topc)).
% 0.19/0.37  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.37  fof(c_0_6, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2))))), inference(assume_negation,[status(cth)],[t48_pre_topc])).
% 0.19/0.37  fof(c_0_7, plain, ![X8, X9, X10]:((m1_subset_1(esk1_3(X8,X9,X10),X8)|r1_tarski(X9,X10)|~m1_subset_1(X10,k1_zfmisc_1(X8))|~m1_subset_1(X9,k1_zfmisc_1(X8)))&((r2_hidden(esk1_3(X8,X9,X10),X9)|r1_tarski(X9,X10)|~m1_subset_1(X10,k1_zfmisc_1(X8))|~m1_subset_1(X9,k1_zfmisc_1(X8)))&(~r2_hidden(esk1_3(X8,X9,X10),X10)|r1_tarski(X9,X10)|~m1_subset_1(X10,k1_zfmisc_1(X8))|~m1_subset_1(X9,k1_zfmisc_1(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).
% 0.19/0.37  fof(c_0_8, plain, ![X14, X15]:(~l1_pre_topc(X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|m1_subset_1(k2_pre_topc(X14,X15),k1_zfmisc_1(u1_struct_0(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.19/0.37  fof(c_0_9, plain, ![X16, X17, X18, X19]:((~r2_hidden(X18,k2_pre_topc(X16,X17))|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))|(~v4_pre_topc(X19,X16)|~r1_tarski(X17,X19)|r2_hidden(X18,X19)))|~r2_hidden(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16))&((m1_subset_1(esk2_3(X16,X17,X18),k1_zfmisc_1(u1_struct_0(X16)))|r2_hidden(X18,k2_pre_topc(X16,X17))|~r2_hidden(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16))&(((v4_pre_topc(esk2_3(X16,X17,X18),X16)|r2_hidden(X18,k2_pre_topc(X16,X17))|~r2_hidden(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16))&(r1_tarski(X17,esk2_3(X16,X17,X18))|r2_hidden(X18,k2_pre_topc(X16,X17))|~r2_hidden(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16)))&(~r2_hidden(X18,esk2_3(X16,X17,X18))|r2_hidden(X18,k2_pre_topc(X16,X17))|~r2_hidden(X18,u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_pre_topc])])])])])).
% 0.19/0.37  fof(c_0_10, negated_conjecture, (l1_pre_topc(esk3_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&~r1_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.19/0.37  fof(c_0_11, plain, ![X5, X6, X7]:(~m1_subset_1(X6,k1_zfmisc_1(X5))|(~r2_hidden(X7,X6)|r2_hidden(X7,X5))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.37  cnf(c_0_12, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_13, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_14, plain, (r1_tarski(X1,esk2_3(X2,X1,X3))|r2_hidden(X3,k2_pre_topc(X2,X1))|~r2_hidden(X3,u1_struct_0(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_17, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_18, plain, (r1_tarski(X1,k2_pre_topc(X2,X3))|r2_hidden(esk1_3(u1_struct_0(X2),X1,k2_pre_topc(X2,X3)),X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (r1_tarski(esk4_0,esk2_3(esk3_0,esk4_0,X1))|r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_17, c_0_15])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (r1_tarski(esk4_0,k2_pre_topc(esk3_0,X1))|r2_hidden(esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,X1)),esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_15]), c_0_16])])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (~r1_tarski(esk4_0,k2_pre_topc(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  fof(c_0_23, plain, ![X12, X13]:((~m1_subset_1(X12,k1_zfmisc_1(X13))|r1_tarski(X12,X13))&(~r1_tarski(X12,X13)|m1_subset_1(X12,k1_zfmisc_1(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (r1_tarski(esk4_0,esk2_3(esk3_0,esk4_0,X1))|r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (r2_hidden(esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0)),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_15]), c_0_22])).
% 0.19/0.37  cnf(c_0_26, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (r1_tarski(esk4_0,esk2_3(esk3_0,esk4_0,esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0))))|r2_hidden(esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0)),k2_pre_topc(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0)),k2_pre_topc(esk3_0,esk4_0))|m1_subset_1(esk4_0,k1_zfmisc_1(esk2_3(esk3_0,esk4_0,esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0)))))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, (r2_hidden(X1,esk2_3(esk3_0,esk4_0,esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0))))|r2_hidden(esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0)),k2_pre_topc(esk3_0,esk4_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_17, c_0_28])).
% 0.19/0.37  cnf(c_0_30, plain, (r2_hidden(X1,k2_pre_topc(X2,X3))|~r2_hidden(X1,esk2_3(X2,X3,X1))|~r2_hidden(X1,u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (r2_hidden(esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0)),esk2_3(esk3_0,esk4_0,esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0))))|r2_hidden(esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0)),k2_pre_topc(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_29, c_0_25])).
% 0.19/0.37  cnf(c_0_32, plain, (r1_tarski(X2,X3)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0)),k2_pre_topc(esk3_0,esk4_0))|~r2_hidden(esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0)),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_16]), c_0_15])])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (~r2_hidden(esk1_3(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,esk4_0)),u1_struct_0(esk3_0))|~m1_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_15])]), c_0_22])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (~m1_subset_1(k2_pre_topc(esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_20]), c_0_25])])).
% 0.19/0.37  cnf(c_0_36, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_13]), c_0_16]), c_0_15])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 37
% 0.19/0.37  # Proof object clause steps            : 24
% 0.19/0.37  # Proof object formula steps           : 13
% 0.19/0.37  # Proof object conjectures             : 19
% 0.19/0.37  # Proof object clause conjectures      : 16
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 10
% 0.19/0.37  # Proof object initial formulas used   : 6
% 0.19/0.37  # Proof object generating inferences   : 14
% 0.19/0.37  # Proof object simplifying inferences  : 16
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 6
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 15
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 15
% 0.19/0.37  # Processed clauses                    : 79
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 2
% 0.19/0.37  # ...remaining for further processing  : 77
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 2
% 0.19/0.37  # Generated clauses                    : 89
% 0.19/0.37  # ...of the previous two non-trivial   : 83
% 0.19/0.37  # Contextual simplify-reflections      : 1
% 0.19/0.37  # Paramodulations                      : 89
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 60
% 0.19/0.37  #    Positive orientable unit clauses  : 6
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 3
% 0.19/0.37  #    Non-unit-clauses                  : 51
% 0.19/0.37  # Current number of unprocessed clauses: 34
% 0.19/0.37  # ...number of literals in the above   : 128
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 17
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 340
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 235
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.19/0.37  # Unit Clause-clause subsumption calls : 26
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 3
% 0.19/0.37  # BW rewrite match successes           : 1
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 4641
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.034 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.037 s
% 0.19/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
