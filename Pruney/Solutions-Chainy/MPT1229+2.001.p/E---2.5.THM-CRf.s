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
% DateTime   : Thu Dec  3 11:10:39 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   25 (  72 expanded)
%              Number of clauses        :   16 (  23 expanded)
%              Number of leaves         :    4 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :  168 ( 454 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X2,X1)
                  & v3_pre_topc(X3,X1) )
               => v3_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_tops_1)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(d1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(X1)
      <=> ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,u1_pre_topc(X1))
               => r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) )
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X1))
                      & r2_hidden(X3,u1_pre_topc(X1)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v3_pre_topc(X2,X1)
                    & v3_pre_topc(X3,X1) )
                 => v3_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t38_tops_1])).

fof(c_0_5,negated_conjecture,
    ( v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & v3_pre_topc(esk5_0,esk4_0)
    & v3_pre_topc(esk6_0,esk4_0)
    & ~ v3_pre_topc(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X14,X15] :
      ( ( ~ v3_pre_topc(X15,X14)
        | r2_hidden(X15,u1_pre_topc(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( ~ r2_hidden(X15,u1_pre_topc(X14))
        | v3_pre_topc(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_7,negated_conjecture,
    ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_10,plain,(
    ! [X4,X5,X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X4))
      | m1_subset_1(k9_subset_1(X4,X5,X6),k1_zfmisc_1(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_11,negated_conjecture,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),u1_pre_topc(esk4_0))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])])).

cnf(c_0_12,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_14,plain,(
    ! [X7,X8,X9,X10] :
      ( ( r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))
        | ~ r1_tarski(X8,u1_pre_topc(X7))
        | r2_hidden(k5_setfam_1(u1_struct_0(X7),X8),u1_pre_topc(X7))
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ r2_hidden(X9,u1_pre_topc(X7))
        | ~ r2_hidden(X10,u1_pre_topc(X7))
        | r2_hidden(k9_subset_1(u1_struct_0(X7),X9,X10),u1_pre_topc(X7))
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk2_1(X7),k1_zfmisc_1(u1_struct_0(X7)))
        | m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk3_1(X7),k1_zfmisc_1(u1_struct_0(X7)))
        | m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( r2_hidden(esk2_1(X7),u1_pre_topc(X7))
        | m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( r2_hidden(esk3_1(X7),u1_pre_topc(X7))
        | m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X7),esk2_1(X7),esk3_1(X7)),u1_pre_topc(X7))
        | m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk2_1(X7),k1_zfmisc_1(u1_struct_0(X7)))
        | r1_tarski(esk1_1(X7),u1_pre_topc(X7))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk3_1(X7),k1_zfmisc_1(u1_struct_0(X7)))
        | r1_tarski(esk1_1(X7),u1_pre_topc(X7))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( r2_hidden(esk2_1(X7),u1_pre_topc(X7))
        | r1_tarski(esk1_1(X7),u1_pre_topc(X7))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( r2_hidden(esk3_1(X7),u1_pre_topc(X7))
        | r1_tarski(esk1_1(X7),u1_pre_topc(X7))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X7),esk2_1(X7),esk3_1(X7)),u1_pre_topc(X7))
        | r1_tarski(esk1_1(X7),u1_pre_topc(X7))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk2_1(X7),k1_zfmisc_1(u1_struct_0(X7)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk3_1(X7),k1_zfmisc_1(u1_struct_0(X7)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( r2_hidden(esk2_1(X7),u1_pre_topc(X7))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( r2_hidden(esk3_1(X7),u1_pre_topc(X7))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X7),esk2_1(X7),esk3_1(X7)),u1_pre_topc(X7))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( v3_pre_topc(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_20,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X2),X1,X3),u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk6_0,u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_9]),c_0_13])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk5_0,u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_17]),c_0_9]),c_0_18])])).

cnf(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_9]),c_0_13]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:16:04 EST 2020
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
% 0.19/0.37  fof(t38_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&v3_pre_topc(X3,X1))=>v3_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_tops_1)).
% 0.19/0.37  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.19/0.37  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 0.19/0.37  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.19/0.37  fof(c_0_4, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&v3_pre_topc(X3,X1))=>v3_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1)))))), inference(assume_negation,[status(cth)],[t38_tops_1])).
% 0.19/0.37  fof(c_0_5, negated_conjecture, ((v2_pre_topc(esk4_0)&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&((v3_pre_topc(esk5_0,esk4_0)&v3_pre_topc(esk6_0,esk4_0))&~v3_pre_topc(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.19/0.37  fof(c_0_6, plain, ![X14, X15]:((~v3_pre_topc(X15,X14)|r2_hidden(X15,u1_pre_topc(X14))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))&(~r2_hidden(X15,u1_pre_topc(X14))|v3_pre_topc(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.19/0.37  cnf(c_0_7, negated_conjecture, (~v3_pre_topc(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_8, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_9, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  fof(c_0_10, plain, ![X4, X5, X6]:(~m1_subset_1(X6,k1_zfmisc_1(X4))|m1_subset_1(k9_subset_1(X4,X5,X6),k1_zfmisc_1(X4))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 0.19/0.37  cnf(c_0_11, negated_conjecture, (~r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),u1_pre_topc(esk4_0))|~m1_subset_1(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9])])).
% 0.19/0.37  cnf(c_0_12, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  fof(c_0_14, plain, ![X7, X8, X9, X10]:((((r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))|~v2_pre_topc(X7)|~l1_pre_topc(X7))&(~m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|(~r1_tarski(X8,u1_pre_topc(X7))|r2_hidden(k5_setfam_1(u1_struct_0(X7),X8),u1_pre_topc(X7)))|~v2_pre_topc(X7)|~l1_pre_topc(X7)))&(~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X7)))|(~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X7)))|(~r2_hidden(X9,u1_pre_topc(X7))|~r2_hidden(X10,u1_pre_topc(X7))|r2_hidden(k9_subset_1(u1_struct_0(X7),X9,X10),u1_pre_topc(X7))))|~v2_pre_topc(X7)|~l1_pre_topc(X7)))&(((m1_subset_1(esk2_1(X7),k1_zfmisc_1(u1_struct_0(X7)))|(m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&((m1_subset_1(esk3_1(X7),k1_zfmisc_1(u1_struct_0(X7)))|(m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&(((r2_hidden(esk2_1(X7),u1_pre_topc(X7))|(m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&(r2_hidden(esk3_1(X7),u1_pre_topc(X7))|(m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7)))&(~r2_hidden(k9_subset_1(u1_struct_0(X7),esk2_1(X7),esk3_1(X7)),u1_pre_topc(X7))|(m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7)))))&(((m1_subset_1(esk2_1(X7),k1_zfmisc_1(u1_struct_0(X7)))|(r1_tarski(esk1_1(X7),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&((m1_subset_1(esk3_1(X7),k1_zfmisc_1(u1_struct_0(X7)))|(r1_tarski(esk1_1(X7),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&(((r2_hidden(esk2_1(X7),u1_pre_topc(X7))|(r1_tarski(esk1_1(X7),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&(r2_hidden(esk3_1(X7),u1_pre_topc(X7))|(r1_tarski(esk1_1(X7),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7)))&(~r2_hidden(k9_subset_1(u1_struct_0(X7),esk2_1(X7),esk3_1(X7)),u1_pre_topc(X7))|(r1_tarski(esk1_1(X7),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7)))))&((m1_subset_1(esk2_1(X7),k1_zfmisc_1(u1_struct_0(X7)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&((m1_subset_1(esk3_1(X7),k1_zfmisc_1(u1_struct_0(X7)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&(((r2_hidden(esk2_1(X7),u1_pre_topc(X7))|(~r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&(r2_hidden(esk3_1(X7),u1_pre_topc(X7))|(~r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7)))&(~r2_hidden(k9_subset_1(u1_struct_0(X7),esk2_1(X7),esk3_1(X7)),u1_pre_topc(X7))|(~r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.19/0.37  cnf(c_0_15, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (v3_pre_topc(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (v3_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (~r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])])).
% 0.19/0.37  cnf(c_0_20, plain, (r2_hidden(k9_subset_1(u1_struct_0(X2),X1,X3),u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,u1_pre_topc(X2))|~r2_hidden(X3,u1_pre_topc(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (r2_hidden(esk6_0,u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_9]), c_0_13])])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (r2_hidden(esk5_0,u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_17]), c_0_9]), c_0_18])])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_9]), c_0_13]), c_0_18])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 25
% 0.19/0.37  # Proof object clause steps            : 16
% 0.19/0.37  # Proof object formula steps           : 9
% 0.19/0.37  # Proof object conjectures             : 15
% 0.19/0.37  # Proof object clause conjectures      : 12
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 11
% 0.19/0.37  # Proof object initial formulas used   : 4
% 0.19/0.37  # Proof object generating inferences   : 5
% 0.19/0.37  # Proof object simplifying inferences  : 17
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 4
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 28
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 28
% 0.19/0.37  # Processed clauses                    : 60
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 60
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 0
% 0.19/0.37  # Generated clauses                    : 21
% 0.19/0.37  # ...of the previous two non-trivial   : 4
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 21
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
% 0.19/0.37  # Current number of processed clauses  : 32
% 0.19/0.37  #    Positive orientable unit clauses  : 8
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 2
% 0.19/0.37  #    Non-unit-clauses                  : 22
% 0.19/0.37  # Current number of unprocessed clauses: 0
% 0.19/0.37  # ...number of literals in the above   : 0
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 28
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 190
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 1
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.37  # Unit Clause-clause subsumption calls : 7
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 0
% 0.19/0.37  # BW rewrite match successes           : 0
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 3532
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.030 s
% 0.19/0.37  # System time              : 0.004 s
% 0.19/0.37  # Total time               : 0.034 s
% 0.19/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
