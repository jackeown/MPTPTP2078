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
% DateTime   : Thu Dec  3 11:08:31 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   23 (  32 expanded)
%              Number of clauses        :   11 (  12 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    5
%              Number of atoms          :  137 ( 158 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(t2_zfmisc_1,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t5_pre_topc,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_pre_topc)).

fof(c_0_6,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X6)))
      | k5_setfam_1(X6,X7) = k3_tarski(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

fof(c_0_7,plain,(
    ! [X5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X5)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_8,plain,(
    ! [X11,X12,X13,X14] :
      ( ( r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | ~ r1_tarski(X12,u1_pre_topc(X11))
        | r2_hidden(k5_setfam_1(u1_struct_0(X11),X12),u1_pre_topc(X11))
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ r2_hidden(X13,u1_pre_topc(X11))
        | ~ r2_hidden(X14,u1_pre_topc(X11))
        | r2_hidden(k9_subset_1(u1_struct_0(X11),X13,X14),u1_pre_topc(X11))
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( m1_subset_1(esk2_1(X11),k1_zfmisc_1(u1_struct_0(X11)))
        | m1_subset_1(esk1_1(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( m1_subset_1(esk3_1(X11),k1_zfmisc_1(u1_struct_0(X11)))
        | m1_subset_1(esk1_1(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( r2_hidden(esk2_1(X11),u1_pre_topc(X11))
        | m1_subset_1(esk1_1(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( r2_hidden(esk3_1(X11),u1_pre_topc(X11))
        | m1_subset_1(esk1_1(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X11),esk2_1(X11),esk3_1(X11)),u1_pre_topc(X11))
        | m1_subset_1(esk1_1(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( m1_subset_1(esk2_1(X11),k1_zfmisc_1(u1_struct_0(X11)))
        | r1_tarski(esk1_1(X11),u1_pre_topc(X11))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( m1_subset_1(esk3_1(X11),k1_zfmisc_1(u1_struct_0(X11)))
        | r1_tarski(esk1_1(X11),u1_pre_topc(X11))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( r2_hidden(esk2_1(X11),u1_pre_topc(X11))
        | r1_tarski(esk1_1(X11),u1_pre_topc(X11))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( r2_hidden(esk3_1(X11),u1_pre_topc(X11))
        | r1_tarski(esk1_1(X11),u1_pre_topc(X11))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X11),esk2_1(X11),esk3_1(X11)),u1_pre_topc(X11))
        | r1_tarski(esk1_1(X11),u1_pre_topc(X11))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( m1_subset_1(esk2_1(X11),k1_zfmisc_1(u1_struct_0(X11)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X11),esk1_1(X11)),u1_pre_topc(X11))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( m1_subset_1(esk3_1(X11),k1_zfmisc_1(u1_struct_0(X11)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X11),esk1_1(X11)),u1_pre_topc(X11))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( r2_hidden(esk2_1(X11),u1_pre_topc(X11))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X11),esk1_1(X11)),u1_pre_topc(X11))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( r2_hidden(esk3_1(X11),u1_pre_topc(X11))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X11),esk1_1(X11)),u1_pre_topc(X11))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X11),esk2_1(X11),esk3_1(X11)),u1_pre_topc(X11))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X11),esk1_1(X11)),u1_pre_topc(X11))
        | ~ r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))
        | v2_pre_topc(X11)
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_9,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X4] : r1_tarski(k1_xboole_0,X4) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => r2_hidden(k1_xboole_0,u1_pre_topc(X1)) ) ),
    inference(assume_negation,[status(cth)],[t5_pre_topc])).

cnf(c_0_14,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k5_setfam_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])).

cnf(c_0_16,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ r2_hidden(k1_xboole_0,u1_pre_topc(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_18,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_10]),c_0_15]),c_0_16])])).

cnf(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( ~ r2_hidden(k1_xboole_0,u1_pre_topc(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.027 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.20/0.37  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.37  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.20/0.37  fof(t2_zfmisc_1, axiom, k3_tarski(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 0.20/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.37  fof(t5_pre_topc, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>r2_hidden(k1_xboole_0,u1_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_pre_topc)).
% 0.20/0.37  fof(c_0_6, plain, ![X6, X7]:(~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X6)))|k5_setfam_1(X6,X7)=k3_tarski(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.20/0.37  fof(c_0_7, plain, ![X5]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X5)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.37  fof(c_0_8, plain, ![X11, X12, X13, X14]:((((r2_hidden(u1_struct_0(X11),u1_pre_topc(X11))|~v2_pre_topc(X11)|~l1_pre_topc(X11))&(~m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))|(~r1_tarski(X12,u1_pre_topc(X11))|r2_hidden(k5_setfam_1(u1_struct_0(X11),X12),u1_pre_topc(X11)))|~v2_pre_topc(X11)|~l1_pre_topc(X11)))&(~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X11)))|(~r2_hidden(X13,u1_pre_topc(X11))|~r2_hidden(X14,u1_pre_topc(X11))|r2_hidden(k9_subset_1(u1_struct_0(X11),X13,X14),u1_pre_topc(X11))))|~v2_pre_topc(X11)|~l1_pre_topc(X11)))&(((m1_subset_1(esk2_1(X11),k1_zfmisc_1(u1_struct_0(X11)))|(m1_subset_1(esk1_1(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11))&((m1_subset_1(esk3_1(X11),k1_zfmisc_1(u1_struct_0(X11)))|(m1_subset_1(esk1_1(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11))&(((r2_hidden(esk2_1(X11),u1_pre_topc(X11))|(m1_subset_1(esk1_1(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11))&(r2_hidden(esk3_1(X11),u1_pre_topc(X11))|(m1_subset_1(esk1_1(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11)))&(~r2_hidden(k9_subset_1(u1_struct_0(X11),esk2_1(X11),esk3_1(X11)),u1_pre_topc(X11))|(m1_subset_1(esk1_1(X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11)))))&(((m1_subset_1(esk2_1(X11),k1_zfmisc_1(u1_struct_0(X11)))|(r1_tarski(esk1_1(X11),u1_pre_topc(X11))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11))&((m1_subset_1(esk3_1(X11),k1_zfmisc_1(u1_struct_0(X11)))|(r1_tarski(esk1_1(X11),u1_pre_topc(X11))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11))&(((r2_hidden(esk2_1(X11),u1_pre_topc(X11))|(r1_tarski(esk1_1(X11),u1_pre_topc(X11))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11))&(r2_hidden(esk3_1(X11),u1_pre_topc(X11))|(r1_tarski(esk1_1(X11),u1_pre_topc(X11))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11)))&(~r2_hidden(k9_subset_1(u1_struct_0(X11),esk2_1(X11),esk3_1(X11)),u1_pre_topc(X11))|(r1_tarski(esk1_1(X11),u1_pre_topc(X11))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11)))))&((m1_subset_1(esk2_1(X11),k1_zfmisc_1(u1_struct_0(X11)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X11),esk1_1(X11)),u1_pre_topc(X11))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11))&((m1_subset_1(esk3_1(X11),k1_zfmisc_1(u1_struct_0(X11)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X11),esk1_1(X11)),u1_pre_topc(X11))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11))&(((r2_hidden(esk2_1(X11),u1_pre_topc(X11))|(~r2_hidden(k5_setfam_1(u1_struct_0(X11),esk1_1(X11)),u1_pre_topc(X11))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11))&(r2_hidden(esk3_1(X11),u1_pre_topc(X11))|(~r2_hidden(k5_setfam_1(u1_struct_0(X11),esk1_1(X11)),u1_pre_topc(X11))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11)))&(~r2_hidden(k9_subset_1(u1_struct_0(X11),esk2_1(X11),esk3_1(X11)),u1_pre_topc(X11))|(~r2_hidden(k5_setfam_1(u1_struct_0(X11),esk1_1(X11)),u1_pre_topc(X11))|~r2_hidden(u1_struct_0(X11),u1_pre_topc(X11)))|v2_pre_topc(X11)|~l1_pre_topc(X11)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.20/0.37  cnf(c_0_9, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  cnf(c_0_10, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_11, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).
% 0.20/0.37  fof(c_0_12, plain, ![X4]:r1_tarski(k1_xboole_0,X4), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.37  fof(c_0_13, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>r2_hidden(k1_xboole_0,u1_pre_topc(X1)))), inference(assume_negation,[status(cth)],[t5_pre_topc])).
% 0.20/0.37  cnf(c_0_14, plain, (r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~r1_tarski(X1,u1_pre_topc(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.37  cnf(c_0_15, plain, (k5_setfam_1(X1,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11])).
% 0.20/0.37  cnf(c_0_16, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.37  fof(c_0_17, negated_conjecture, ((v2_pre_topc(esk4_0)&l1_pre_topc(esk4_0))&~r2_hidden(k1_xboole_0,u1_pre_topc(esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.20/0.37  cnf(c_0_18, plain, (r2_hidden(k1_xboole_0,u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_10]), c_0_15]), c_0_16])])).
% 0.20/0.37  cnf(c_0_19, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.37  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.37  cnf(c_0_21, negated_conjecture, (~r2_hidden(k1_xboole_0,u1_pre_topc(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.37  cnf(c_0_22, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])]), c_0_21]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 23
% 0.20/0.37  # Proof object clause steps            : 11
% 0.20/0.37  # Proof object formula steps           : 12
% 0.20/0.37  # Proof object conjectures             : 7
% 0.20/0.37  # Proof object clause conjectures      : 4
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 8
% 0.20/0.37  # Proof object initial formulas used   : 6
% 0.20/0.37  # Proof object generating inferences   : 3
% 0.20/0.37  # Proof object simplifying inferences  : 7
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 7
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 26
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 26
% 0.20/0.37  # Processed clauses                    : 57
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 4
% 0.20/0.37  # ...remaining for further processing  : 53
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 0
% 0.20/0.37  # Generated clauses                    : 35
% 0.20/0.37  # ...of the previous two non-trivial   : 25
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 35
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 0
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 27
% 0.20/0.37  #    Positive orientable unit clauses  : 6
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 1
% 0.20/0.37  #    Non-unit-clauses                  : 20
% 0.20/0.37  # Current number of unprocessed clauses: 20
% 0.20/0.37  # ...number of literals in the above   : 108
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 26
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 267
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 19
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 4
% 0.20/0.37  # Unit Clause-clause subsumption calls : 0
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 0
% 0.20/0.37  # BW rewrite match successes           : 0
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 3203
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.030 s
% 0.20/0.37  # System time              : 0.004 s
% 0.20/0.37  # Total time               : 0.034 s
% 0.20/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
