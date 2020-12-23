%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:01 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   37 (  99 expanded)
%              Number of clauses        :   24 (  37 expanded)
%              Number of leaves         :    6 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :  115 ( 452 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( ( r1_tarski(X2,X3)
                  & v1_tops_2(X3,X1) )
               => v1_tops_2(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(d1_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ( ( r1_tarski(X2,X3)
                    & v1_tops_2(X3,X1) )
                 => v1_tops_2(X2,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_tops_2])).

fof(c_0_7,plain,(
    ! [X6,X7] :
      ( ( ~ m1_subset_1(X6,k1_zfmisc_1(X7))
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | m1_subset_1(X6,k1_zfmisc_1(X7)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_8,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    & r1_tarski(esk3_0,esk4_0)
    & v1_tops_2(esk4_0,esk2_0)
    & ~ v1_tops_2(esk3_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X8,X9,X10] :
      ( ~ r2_hidden(X8,X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X10))
      | m1_subset_1(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_10,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X14,X15,X16] :
      ( ( ~ v1_tops_2(X15,X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ r2_hidden(X16,X15)
        | v3_pre_topc(X16,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk1_2(X14,X15),k1_zfmisc_1(u1_struct_0(X14)))
        | v1_tops_2(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | ~ l1_pre_topc(X14) )
      & ( r2_hidden(esk1_2(X14,X15),X15)
        | v1_tops_2(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | ~ l1_pre_topc(X14) )
      & ( ~ v3_pre_topc(esk1_2(X14,X15),X14)
        | v1_tops_2(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).

fof(c_0_13,plain,(
    ! [X11,X12,X13] :
      ( ~ r2_hidden(X11,X12)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X13))
      | ~ v1_xboole_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( ~ v1_tops_2(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_22,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,X5)
      | v1_xboole_0(X5)
      | r2_hidden(X4,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk1_2(esk2_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(X1,esk3_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_15])).

cnf(c_0_26,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v1_tops_2(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[c_0_21,c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,negated_conjecture,
    ( v1_tops_2(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk1_2(esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_32,plain,
    ( v1_tops_2(X2,X1)
    | ~ v3_pre_topc(esk1_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_18])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_2(esk2_0,esk3_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( ~ v3_pre_topc(esk1_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:45:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S072A
% 0.12/0.39  # and selection function SelectCQArEqFirst.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.044 s
% 0.12/0.39  # Presaturation interreduction done
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(t18_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>((r1_tarski(X2,X3)&v1_tops_2(X3,X1))=>v1_tops_2(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tops_2)).
% 0.12/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.12/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.12/0.39  fof(d1_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_2)).
% 0.12/0.39  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.12/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.12/0.39  fof(c_0_6, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>((r1_tarski(X2,X3)&v1_tops_2(X3,X1))=>v1_tops_2(X2,X1)))))), inference(assume_negation,[status(cth)],[t18_tops_2])).
% 0.12/0.39  fof(c_0_7, plain, ![X6, X7]:((~m1_subset_1(X6,k1_zfmisc_1(X7))|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|m1_subset_1(X6,k1_zfmisc_1(X7)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.12/0.39  fof(c_0_8, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))&((r1_tarski(esk3_0,esk4_0)&v1_tops_2(esk4_0,esk2_0))&~v1_tops_2(esk3_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.12/0.39  fof(c_0_9, plain, ![X8, X9, X10]:(~r2_hidden(X8,X9)|~m1_subset_1(X9,k1_zfmisc_1(X10))|m1_subset_1(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.12/0.39  cnf(c_0_10, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.39  cnf(c_0_11, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.39  fof(c_0_12, plain, ![X14, X15, X16]:((~v1_tops_2(X15,X14)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(~r2_hidden(X16,X15)|v3_pre_topc(X16,X14)))|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))|~l1_pre_topc(X14))&((m1_subset_1(esk1_2(X14,X15),k1_zfmisc_1(u1_struct_0(X14)))|v1_tops_2(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))|~l1_pre_topc(X14))&((r2_hidden(esk1_2(X14,X15),X15)|v1_tops_2(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))|~l1_pre_topc(X14))&(~v3_pre_topc(esk1_2(X14,X15),X14)|v1_tops_2(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))|~l1_pre_topc(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).
% 0.12/0.39  fof(c_0_13, plain, ![X11, X12, X13]:(~r2_hidden(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(X13))|~v1_xboole_0(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.12/0.39  cnf(c_0_14, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.12/0.39  cnf(c_0_16, plain, (r2_hidden(esk1_2(X1,X2),X2)|v1_tops_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.39  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.39  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.39  cnf(c_0_19, negated_conjecture, (~v1_tops_2(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.39  cnf(c_0_20, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.39  cnf(c_0_21, plain, (v3_pre_topc(X3,X2)|~v1_tops_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.39  fof(c_0_22, plain, ![X4, X5]:(~m1_subset_1(X4,X5)|(v1_xboole_0(X5)|r2_hidden(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.12/0.39  cnf(c_0_23, negated_conjecture, (m1_subset_1(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.39  cnf(c_0_24, negated_conjecture, (r2_hidden(esk1_2(esk2_0,esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])]), c_0_19])).
% 0.12/0.39  cnf(c_0_25, negated_conjecture, (~r2_hidden(X1,esk3_0)|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_15])).
% 0.12/0.39  cnf(c_0_26, plain, (v3_pre_topc(X1,X2)|~v1_tops_2(X3,X2)|~l1_pre_topc(X2)|~r2_hidden(X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))), inference(csr,[status(thm)],[c_0_21, c_0_14])).
% 0.12/0.39  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.39  cnf(c_0_28, negated_conjecture, (v1_tops_2(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.39  cnf(c_0_29, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.39  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk1_2(esk2_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.39  cnf(c_0_31, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_24])).
% 0.12/0.39  cnf(c_0_32, plain, (v1_tops_2(X2,X1)|~v3_pre_topc(esk1_2(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.39  cnf(c_0_33, negated_conjecture, (v3_pre_topc(X1,esk2_0)|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_18])])).
% 0.12/0.39  cnf(c_0_34, negated_conjecture, (r2_hidden(esk1_2(esk2_0,esk3_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.12/0.39  cnf(c_0_35, negated_conjecture, (~v3_pre_topc(esk1_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_17]), c_0_18])]), c_0_19])).
% 0.12/0.39  cnf(c_0_36, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 37
% 0.12/0.39  # Proof object clause steps            : 24
% 0.12/0.39  # Proof object formula steps           : 13
% 0.12/0.39  # Proof object conjectures             : 19
% 0.12/0.39  # Proof object clause conjectures      : 16
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 13
% 0.12/0.39  # Proof object initial formulas used   : 6
% 0.12/0.39  # Proof object generating inferences   : 10
% 0.12/0.39  # Proof object simplifying inferences  : 12
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 6
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 15
% 0.12/0.39  # Removed in clause preprocessing      : 0
% 0.12/0.39  # Initial clauses in saturation        : 15
% 0.12/0.39  # Processed clauses                    : 51
% 0.12/0.39  # ...of these trivial                  : 0
% 0.12/0.39  # ...subsumed                          : 0
% 0.12/0.39  # ...remaining for further processing  : 51
% 0.12/0.39  # Other redundant clauses eliminated   : 0
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 0
% 0.12/0.39  # Backward-rewritten                   : 0
% 0.12/0.39  # Generated clauses                    : 36
% 0.12/0.39  # ...of the previous two non-trivial   : 26
% 0.12/0.39  # Contextual simplify-reflections      : 1
% 0.12/0.39  # Paramodulations                      : 36
% 0.12/0.39  # Factorizations                       : 0
% 0.12/0.39  # Equation resolutions                 : 0
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 36
% 0.12/0.39  #    Positive orientable unit clauses  : 13
% 0.12/0.39  #    Positive unorientable unit clauses: 0
% 0.12/0.39  #    Negative unit clauses             : 4
% 0.12/0.39  #    Non-unit-clauses                  : 19
% 0.12/0.39  # Current number of unprocessed clauses: 5
% 0.12/0.39  # ...number of literals in the above   : 10
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 15
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 68
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 19
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 1
% 0.12/0.39  # Unit Clause-clause subsumption calls : 28
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 0
% 0.12/0.39  # BW rewrite match successes           : 0
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 1714
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.048 s
% 0.12/0.39  # System time              : 0.004 s
% 0.12/0.39  # Total time               : 0.052 s
% 0.12/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
