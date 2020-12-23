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
% DateTime   : Thu Dec  3 11:10:39 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   30 (  83 expanded)
%              Number of clauses        :   19 (  30 expanded)
%              Number of leaves         :    5 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :  185 ( 463 expanded)
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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

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

fof(c_0_5,negated_conjecture,(
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

fof(c_0_6,negated_conjecture,
    ( v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & v3_pre_topc(esk5_0,esk4_0)
    & v3_pre_topc(esk6_0,esk4_0)
    & ~ v3_pre_topc(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_7,plain,(
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

fof(c_0_8,plain,(
    ! [X4,X5,X6] :
      ( ~ r2_hidden(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X6))
      | m1_subset_1(X4,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_9,plain,(
    ! [X16] :
      ( ~ l1_pre_topc(X16)
      | m1_subset_1(u1_pre_topc(X16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_10,negated_conjecture,
    ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
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

cnf(c_0_16,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X2),X1,X3),u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,negated_conjecture,
    ( v3_pre_topc(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_12])])).

cnf(c_0_25,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X3,u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_18,c_0_17]),c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk6_0,u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_12]),c_0_21])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk5_0,u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_22]),c_0_12]),c_0_23])])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_12]),c_0_27]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t38_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&v3_pre_topc(X3,X1))=>v3_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_tops_1)).
% 0.20/0.38  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.20/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.38  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.20/0.38  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.20/0.38  fof(c_0_5, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&v3_pre_topc(X3,X1))=>v3_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1)))))), inference(assume_negation,[status(cth)],[t38_tops_1])).
% 0.20/0.38  fof(c_0_6, negated_conjecture, ((v2_pre_topc(esk4_0)&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&((v3_pre_topc(esk5_0,esk4_0)&v3_pre_topc(esk6_0,esk4_0))&~v3_pre_topc(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.20/0.38  fof(c_0_7, plain, ![X14, X15]:((~v3_pre_topc(X15,X14)|r2_hidden(X15,u1_pre_topc(X14))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))&(~r2_hidden(X15,u1_pre_topc(X14))|v3_pre_topc(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.20/0.38  fof(c_0_8, plain, ![X4, X5, X6]:(~r2_hidden(X4,X5)|~m1_subset_1(X5,k1_zfmisc_1(X6))|m1_subset_1(X4,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.38  fof(c_0_9, plain, ![X16]:(~l1_pre_topc(X16)|m1_subset_1(u1_pre_topc(X16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.20/0.38  cnf(c_0_10, negated_conjecture, (~v3_pre_topc(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_11, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_12, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_13, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_14, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  fof(c_0_15, plain, ![X7, X8, X9, X10]:((((r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))|~v2_pre_topc(X7)|~l1_pre_topc(X7))&(~m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|(~r1_tarski(X8,u1_pre_topc(X7))|r2_hidden(k5_setfam_1(u1_struct_0(X7),X8),u1_pre_topc(X7)))|~v2_pre_topc(X7)|~l1_pre_topc(X7)))&(~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X7)))|(~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X7)))|(~r2_hidden(X9,u1_pre_topc(X7))|~r2_hidden(X10,u1_pre_topc(X7))|r2_hidden(k9_subset_1(u1_struct_0(X7),X9,X10),u1_pre_topc(X7))))|~v2_pre_topc(X7)|~l1_pre_topc(X7)))&(((m1_subset_1(esk2_1(X7),k1_zfmisc_1(u1_struct_0(X7)))|(m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&((m1_subset_1(esk3_1(X7),k1_zfmisc_1(u1_struct_0(X7)))|(m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&(((r2_hidden(esk2_1(X7),u1_pre_topc(X7))|(m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&(r2_hidden(esk3_1(X7),u1_pre_topc(X7))|(m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7)))&(~r2_hidden(k9_subset_1(u1_struct_0(X7),esk2_1(X7),esk3_1(X7)),u1_pre_topc(X7))|(m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7)))))&(((m1_subset_1(esk2_1(X7),k1_zfmisc_1(u1_struct_0(X7)))|(r1_tarski(esk1_1(X7),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&((m1_subset_1(esk3_1(X7),k1_zfmisc_1(u1_struct_0(X7)))|(r1_tarski(esk1_1(X7),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&(((r2_hidden(esk2_1(X7),u1_pre_topc(X7))|(r1_tarski(esk1_1(X7),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&(r2_hidden(esk3_1(X7),u1_pre_topc(X7))|(r1_tarski(esk1_1(X7),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7)))&(~r2_hidden(k9_subset_1(u1_struct_0(X7),esk2_1(X7),esk3_1(X7)),u1_pre_topc(X7))|(r1_tarski(esk1_1(X7),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7)))))&((m1_subset_1(esk2_1(X7),k1_zfmisc_1(u1_struct_0(X7)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&((m1_subset_1(esk3_1(X7),k1_zfmisc_1(u1_struct_0(X7)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&(((r2_hidden(esk2_1(X7),u1_pre_topc(X7))|(~r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&(r2_hidden(esk3_1(X7),u1_pre_topc(X7))|(~r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7)))&(~r2_hidden(k9_subset_1(u1_struct_0(X7),esk2_1(X7),esk3_1(X7)),u1_pre_topc(X7))|(~r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.20/0.38  cnf(c_0_16, negated_conjecture, (~m1_subset_1(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])])).
% 0.20/0.38  cnf(c_0_17, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)|~r2_hidden(X1,u1_pre_topc(X2))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.38  cnf(c_0_18, plain, (r2_hidden(k9_subset_1(u1_struct_0(X2),X1,X3),u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,u1_pre_topc(X2))|~r2_hidden(X3,u1_pre_topc(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_19, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (v3_pre_topc(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (v3_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (~r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_12])])).
% 0.20/0.38  cnf(c_0_25, plain, (r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~r2_hidden(X3,u1_pre_topc(X1))|~r2_hidden(X2,u1_pre_topc(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_18, c_0_17]), c_0_17])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (r2_hidden(esk6_0,u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_12]), c_0_21])])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(esk5_0,u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_22]), c_0_12]), c_0_23])])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_12]), c_0_27]), c_0_28])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 30
% 0.20/0.38  # Proof object clause steps            : 19
% 0.20/0.38  # Proof object formula steps           : 11
% 0.20/0.38  # Proof object conjectures             : 15
% 0.20/0.38  # Proof object clause conjectures      : 12
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 12
% 0.20/0.38  # Proof object initial formulas used   : 5
% 0.20/0.38  # Proof object generating inferences   : 6
% 0.20/0.38  # Proof object simplifying inferences  : 17
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 5
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 29
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 29
% 0.20/0.38  # Processed clauses                    : 70
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 2
% 0.20/0.38  # ...remaining for further processing  : 68
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 0
% 0.20/0.38  # Generated clauses                    : 30
% 0.20/0.38  # ...of the previous two non-trivial   : 13
% 0.20/0.38  # Contextual simplify-reflections      : 2
% 0.20/0.38  # Paramodulations                      : 30
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
% 0.20/0.38  # Current number of processed clauses  : 39
% 0.20/0.38  #    Positive orientable unit clauses  : 8
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 29
% 0.20/0.38  # Current number of unprocessed clauses: 0
% 0.20/0.38  # ...number of literals in the above   : 0
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 29
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 410
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 61
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 4
% 0.20/0.38  # Unit Clause-clause subsumption calls : 7
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 0
% 0.20/0.38  # BW rewrite match successes           : 0
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3803
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.032 s
% 0.20/0.38  # System time              : 0.003 s
% 0.20/0.38  # Total time               : 0.034 s
% 0.20/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
