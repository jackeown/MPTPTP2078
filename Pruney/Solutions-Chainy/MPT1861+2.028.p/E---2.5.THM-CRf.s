%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:38 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 190 expanded)
%              Number of clauses        :   37 (  79 expanded)
%              Number of leaves         :    9 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  139 ( 545 expanded)
%              Number of equality atoms :   11 (  79 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t29_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v2_tex_2(X2,X1)
                  | v2_tex_2(X3,X1) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

fof(t28_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r1_tarski(X3,X2)
                  & v2_tex_2(X2,X1) )
               => v2_tex_2(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_9,plain,(
    ! [X10,X11] : r1_tarski(k3_xboole_0(X10,X11),X10) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_10,plain,(
    ! [X20,X21] : k1_setfam_1(k2_tarski(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_11,plain,(
    ! [X12,X13] : k2_enumset1(X12,X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_12,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X17))
      | k9_subset_1(X17,X18,X19) = k3_xboole_0(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_13,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_14,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_21,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_enumset1(X3,X3,X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_15]),c_0_16])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v2_tex_2(X2,X1)
                    | v2_tex_2(X3,X1) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_tex_2])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r1_tarski(k9_subset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( v2_tex_2(esk3_0,esk2_0)
      | v2_tex_2(esk4_0,esk2_0) )
    & ~ v2_tex_2(k9_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

fof(c_0_26,plain,(
    ! [X24,X25,X26] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ r1_tarski(X26,X25)
      | ~ v2_tex_2(X25,X24)
      | v2_tex_2(X26,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_tex_2])])])).

fof(c_0_27,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X14))
      | m1_subset_1(k9_subset_1(X14,X15,X16),k1_zfmisc_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_2(k9_subset_1(X1,X2,X3),X4),X2)
    | r1_tarski(k9_subset_1(X1,X2,X3),X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( v2_tex_2(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | ~ v2_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_2(k9_subset_1(u1_struct_0(esk2_0),X1,esk4_0),X2),X1)
    | r1_tarski(k9_subset_1(u1_struct_0(esk2_0),X1,esk4_0),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k9_subset_1(X1,X2,X3) = k9_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_21])).

cnf(c_0_36,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v2_tex_2(X4,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(X1),X2,X3),X4) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k9_subset_1(u1_struct_0(esk2_0),X1,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(X1,esk3_0,esk4_0),esk2_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_29])])).

cnf(c_0_40,negated_conjecture,
    ( v2_tex_2(k9_subset_1(u1_struct_0(esk2_0),X1,esk4_0),esk2_0)
    | ~ v2_tex_2(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_29])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_42,negated_conjecture,
    ( v2_tex_2(esk3_0,esk2_0)
    | v2_tex_2(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_tex_2(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_29]),c_0_41])])).

cnf(c_0_44,plain,
    ( v2_tex_2(k9_subset_1(X1,X2,X3),X4)
    | ~ v2_tex_2(X5,X4)
    | ~ l1_pre_topc(X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r1_tarski(k9_subset_1(X1,X2,X3),X5) ),
    inference(spm,[status(thm)],[c_0_36,c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( v2_tex_2(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( v2_tex_2(k9_subset_1(X1,X2,X3),esk2_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r1_tarski(k9_subset_1(X1,X2,X3),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_29]),c_0_45]),c_0_38])])).

fof(c_0_47,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X22,k1_zfmisc_1(X23))
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(X22,X23)
        | m1_subset_1(X22,k1_zfmisc_1(X23)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_48,negated_conjecture,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_46]),c_0_29])])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,plain,
    ( m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_35])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n013.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 14:13:24 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.11/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.11/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.11/0.37  #
% 0.11/0.37  # Preprocessing time       : 0.027 s
% 0.11/0.37  # Presaturation interreduction done
% 0.11/0.37  
% 0.11/0.37  # Proof found!
% 0.11/0.37  # SZS status Theorem
% 0.11/0.37  # SZS output start CNFRefutation
% 0.11/0.37  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.11/0.37  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.11/0.37  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 0.11/0.37  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.11/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.11/0.37  fof(t29_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X2,X1)|v2_tex_2(X3,X1))=>v2_tex_2(k9_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 0.11/0.37  fof(t28_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_tarski(X3,X2)&v2_tex_2(X2,X1))=>v2_tex_2(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 0.11/0.37  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 0.11/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.11/0.37  fof(c_0_9, plain, ![X10, X11]:r1_tarski(k3_xboole_0(X10,X11),X10), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.11/0.37  fof(c_0_10, plain, ![X20, X21]:k1_setfam_1(k2_tarski(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.11/0.37  fof(c_0_11, plain, ![X12, X13]:k2_enumset1(X12,X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.11/0.37  fof(c_0_12, plain, ![X17, X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(X17))|k9_subset_1(X17,X18,X19)=k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.11/0.37  fof(c_0_13, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.11/0.37  cnf(c_0_14, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.11/0.37  cnf(c_0_15, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.11/0.37  cnf(c_0_16, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.11/0.37  cnf(c_0_17, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.37  cnf(c_0_18, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.11/0.37  cnf(c_0_19, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.11/0.37  cnf(c_0_20, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.11/0.37  cnf(c_0_21, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_enumset1(X3,X3,X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_15]), c_0_16])).
% 0.11/0.37  fof(c_0_22, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X2,X1)|v2_tex_2(X3,X1))=>v2_tex_2(k9_subset_1(u1_struct_0(X1),X2,X3),X1)))))), inference(assume_negation,[status(cth)],[t29_tex_2])).
% 0.11/0.37  cnf(c_0_23, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.11/0.37  cnf(c_0_24, plain, (r1_tarski(k9_subset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.11/0.37  fof(c_0_25, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((v2_tex_2(esk3_0,esk2_0)|v2_tex_2(esk4_0,esk2_0))&~v2_tex_2(k9_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0),esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.11/0.37  fof(c_0_26, plain, ![X24, X25, X26]:(~l1_pre_topc(X24)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|(~r1_tarski(X26,X25)|~v2_tex_2(X25,X24)|v2_tex_2(X26,X24))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_tex_2])])])).
% 0.11/0.37  fof(c_0_27, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(X14))|m1_subset_1(k9_subset_1(X14,X15,X16),k1_zfmisc_1(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 0.11/0.37  cnf(c_0_28, plain, (r2_hidden(esk1_2(k9_subset_1(X1,X2,X3),X4),X2)|r1_tarski(k9_subset_1(X1,X2,X3),X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.11/0.37  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.11/0.37  cnf(c_0_30, plain, (v2_tex_2(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X3,X2)|~v2_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.11/0.37  cnf(c_0_31, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.11/0.37  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.11/0.37  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_2(k9_subset_1(u1_struct_0(esk2_0),X1,esk4_0),X2),X1)|r1_tarski(k9_subset_1(u1_struct_0(esk2_0),X1,esk4_0),X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.11/0.37  cnf(c_0_34, negated_conjecture, (~v2_tex_2(k9_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.11/0.37  cnf(c_0_35, plain, (k9_subset_1(X1,X2,X3)=k9_subset_1(X4,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_21, c_0_21])).
% 0.11/0.37  cnf(c_0_36, plain, (v2_tex_2(k9_subset_1(u1_struct_0(X1),X2,X3),X1)|~v2_tex_2(X4,X1)|~l1_pre_topc(X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k9_subset_1(u1_struct_0(X1),X2,X3),X4)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.11/0.37  cnf(c_0_37, negated_conjecture, (r1_tarski(k9_subset_1(u1_struct_0(esk2_0),X1,esk4_0),X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.11/0.37  cnf(c_0_38, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.11/0.37  cnf(c_0_39, negated_conjecture, (~v2_tex_2(k9_subset_1(X1,esk3_0,esk4_0),esk2_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_29])])).
% 0.11/0.37  cnf(c_0_40, negated_conjecture, (v2_tex_2(k9_subset_1(u1_struct_0(esk2_0),X1,esk4_0),esk2_0)|~v2_tex_2(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_29])])).
% 0.11/0.37  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.11/0.37  cnf(c_0_42, negated_conjecture, (v2_tex_2(esk3_0,esk2_0)|v2_tex_2(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.11/0.37  cnf(c_0_43, negated_conjecture, (~v2_tex_2(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_29]), c_0_41])])).
% 0.11/0.37  cnf(c_0_44, plain, (v2_tex_2(k9_subset_1(X1,X2,X3),X4)|~v2_tex_2(X5,X4)|~l1_pre_topc(X4)|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~r1_tarski(k9_subset_1(X1,X2,X3),X5)), inference(spm,[status(thm)],[c_0_36, c_0_35])).
% 0.11/0.37  cnf(c_0_45, negated_conjecture, (v2_tex_2(esk4_0,esk2_0)), inference(sr,[status(thm)],[c_0_42, c_0_43])).
% 0.11/0.37  cnf(c_0_46, negated_conjecture, (v2_tex_2(k9_subset_1(X1,X2,X3),esk2_0)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~r1_tarski(k9_subset_1(X1,X2,X3),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_29]), c_0_45]), c_0_38])])).
% 0.11/0.37  fof(c_0_47, plain, ![X22, X23]:((~m1_subset_1(X22,k1_zfmisc_1(X23))|r1_tarski(X22,X23))&(~r1_tarski(X22,X23)|m1_subset_1(X22,k1_zfmisc_1(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.11/0.37  cnf(c_0_48, negated_conjecture, (~r1_tarski(k9_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_46]), c_0_29])])).
% 0.11/0.37  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.11/0.37  cnf(c_0_50, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.11/0.37  cnf(c_0_51, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_32, c_0_19])).
% 0.11/0.37  cnf(c_0_52, negated_conjecture, (~m1_subset_1(k9_subset_1(u1_struct_0(esk2_0),esk3_0,esk4_0),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.11/0.37  cnf(c_0_53, plain, (m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_31, c_0_35])).
% 0.11/0.37  cnf(c_0_54, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.11/0.37  cnf(c_0_55, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_29])]), ['proof']).
% 0.11/0.37  # SZS output end CNFRefutation
% 0.11/0.37  # Proof object total steps             : 56
% 0.11/0.37  # Proof object clause steps            : 37
% 0.11/0.37  # Proof object formula steps           : 19
% 0.11/0.37  # Proof object conjectures             : 18
% 0.11/0.37  # Proof object clause conjectures      : 15
% 0.11/0.37  # Proof object formula conjectures     : 3
% 0.11/0.37  # Proof object initial clauses used    : 16
% 0.11/0.37  # Proof object initial formulas used   : 9
% 0.11/0.37  # Proof object generating inferences   : 18
% 0.11/0.37  # Proof object simplifying inferences  : 21
% 0.11/0.37  # Training examples: 0 positive, 0 negative
% 0.11/0.37  # Parsed axioms                        : 9
% 0.11/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.37  # Initial clauses                      : 16
% 0.11/0.37  # Removed in clause preprocessing      : 2
% 0.11/0.37  # Initial clauses in saturation        : 14
% 0.11/0.37  # Processed clauses                    : 333
% 0.11/0.37  # ...of these trivial                  : 0
% 0.11/0.37  # ...subsumed                          : 179
% 0.11/0.37  # ...remaining for further processing  : 154
% 0.11/0.37  # Other redundant clauses eliminated   : 0
% 0.11/0.37  # Clauses deleted for lack of memory   : 0
% 0.11/0.37  # Backward-subsumed                    : 4
% 0.11/0.37  # Backward-rewritten                   : 12
% 0.11/0.37  # Generated clauses                    : 467
% 0.11/0.37  # ...of the previous two non-trivial   : 452
% 0.11/0.37  # Contextual simplify-reflections      : 4
% 0.11/0.37  # Paramodulations                      : 466
% 0.11/0.37  # Factorizations                       : 0
% 0.11/0.37  # Equation resolutions                 : 0
% 0.11/0.37  # Propositional unsat checks           : 0
% 0.11/0.37  #    Propositional check models        : 0
% 0.11/0.37  #    Propositional check unsatisfiable : 0
% 0.11/0.37  #    Propositional clauses             : 0
% 0.11/0.37  #    Propositional clauses after purity: 0
% 0.11/0.37  #    Propositional unsat core size     : 0
% 0.11/0.37  #    Propositional preprocessing time  : 0.000
% 0.11/0.37  #    Propositional encoding time       : 0.000
% 0.11/0.37  #    Propositional solver time         : 0.000
% 0.11/0.37  #    Success case prop preproc time    : 0.000
% 0.11/0.37  #    Success case prop encoding time   : 0.000
% 0.11/0.37  #    Success case prop solver time     : 0.000
% 0.11/0.37  # Current number of processed clauses  : 123
% 0.11/0.37  #    Positive orientable unit clauses  : 14
% 0.11/0.37  #    Positive unorientable unit clauses: 0
% 0.11/0.37  #    Negative unit clauses             : 8
% 0.11/0.37  #    Non-unit-clauses                  : 101
% 0.11/0.37  # Current number of unprocessed clauses: 136
% 0.11/0.37  # ...number of literals in the above   : 574
% 0.11/0.37  # Current number of archived formulas  : 0
% 0.11/0.37  # Current number of archived clauses   : 33
% 0.11/0.37  # Clause-clause subsumption calls (NU) : 2635
% 0.11/0.37  # Rec. Clause-clause subsumption calls : 937
% 0.11/0.37  # Non-unit clause-clause subsumptions  : 172
% 0.11/0.37  # Unit Clause-clause subsumption calls : 201
% 0.11/0.37  # Rewrite failures with RHS unbound    : 0
% 0.11/0.37  # BW rewrite match attempts            : 18
% 0.11/0.37  # BW rewrite match successes           : 3
% 0.11/0.37  # Condensation attempts                : 0
% 0.11/0.37  # Condensation successes               : 0
% 0.11/0.37  # Termbank termtop insertions          : 11425
% 0.11/0.38  
% 0.11/0.38  # -------------------------------------------------
% 0.11/0.38  # User time                : 0.047 s
% 0.11/0.38  # System time              : 0.003 s
% 0.11/0.38  # Total time               : 0.050 s
% 0.11/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
