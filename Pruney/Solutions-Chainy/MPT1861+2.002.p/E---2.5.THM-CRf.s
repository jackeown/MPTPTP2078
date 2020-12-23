%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:34 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 587 expanded)
%              Number of clauses        :   46 ( 262 expanded)
%              Number of leaves         :    9 ( 152 expanded)
%              Depth                    :   13
%              Number of atoms          :  133 (1318 expanded)
%              Number of equality atoms :   22 ( 330 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

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

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(c_0_9,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(X26))
      | k9_subset_1(X26,X27,X28) = k3_xboole_0(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_10,plain,(
    ! [X29,X30] : k1_setfam_1(k2_tarski(X29,X30)) = k3_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_11,plain,(
    ! [X24,X25] : k2_enumset1(X24,X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X20,X21] : r1_tarski(k3_xboole_0(X20,X21),X20) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_14,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ( v2_tex_2(esk4_0,esk3_0)
      | v2_tex_2(esk5_0,esk3_0) )
    & ~ v2_tex_2(k9_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_18,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_19,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_enumset1(X3,X3,X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X22,X23] : k2_tarski(X22,X23) = k2_tarski(X23,X22) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_23,plain,(
    ! [X31,X32] :
      ( ( ~ m1_subset_1(X31,k1_zfmisc_1(X32))
        | r1_tarski(X31,X32) )
      & ( ~ r1_tarski(X31,X32)
        | m1_subset_1(X31,k1_zfmisc_1(X32)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_15]),c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,esk5_0)) = k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_16]),c_0_16])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_2(k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0),X2),X1)
    | r1_tarski(k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,X1)) = k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_34])).

cnf(c_0_40,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k9_subset_1(X2,X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_35])).

fof(c_0_41,plain,(
    ! [X33,X34,X35] :
      ( ~ l1_pre_topc(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
      | ~ r1_tarski(X35,X34)
      | ~ v2_tex_2(X34,X33)
      | v2_tex_2(X35,X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_tex_2])])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk1_2(k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0),X2),X3)
    | r1_tarski(k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0),X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( k9_subset_1(X1,esk5_0,X1) = k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk3_0),X1,esk4_0) = k1_setfam_1(k2_enumset1(X1,X1,X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_38])).

cnf(c_0_46,plain,
    ( v2_tex_2(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | ~ v2_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk1_2(k9_subset_1(esk4_0,esk5_0,esk4_0),X1),u1_struct_0(esk3_0))
    | r1_tarski(k9_subset_1(esk4_0,esk5_0,esk4_0),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk3_0),esk5_0,esk4_0) = k9_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk3_0),X1,esk4_0) = k9_subset_1(esk4_0,X1,esk4_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( v2_tex_2(X1,esk3_0)
    | ~ v2_tex_2(X2,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( v2_tex_2(esk4_0,esk3_0)
    | v2_tex_2(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k9_subset_1(esk4_0,esk5_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_55,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_0) = k9_subset_1(esk4_0,esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( v2_tex_2(esk4_0,esk3_0)
    | v2_tex_2(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_21])])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(k9_subset_1(esk4_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_53])).

cnf(c_0_58,plain,
    ( r1_tarski(k9_subset_1(X1,X2,X1),X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_40])).

cnf(c_0_59,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(esk4_0,esk5_0,esk4_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( v2_tex_2(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])]),c_0_59])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_34])).

cnf(c_0_62,negated_conjecture,
    ( v2_tex_2(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_60]),c_0_38])])).

cnf(c_0_63,plain,
    ( r1_tarski(k9_subset_1(X1,X2,X1),X1) ),
    inference(rw,[status(thm)],[c_0_61,c_0_40])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_57]),c_0_63])]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:57:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 3.06/3.34  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S002A
% 3.06/3.34  # and selection function SelectNegativeLiterals.
% 3.06/3.34  #
% 3.06/3.34  # Preprocessing time       : 0.027 s
% 3.06/3.34  # Presaturation interreduction done
% 3.06/3.34  
% 3.06/3.34  # Proof found!
% 3.06/3.34  # SZS status Theorem
% 3.06/3.34  # SZS output start CNFRefutation
% 3.06/3.34  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.06/3.34  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.06/3.34  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 3.06/3.34  fof(t29_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X2,X1)|v2_tex_2(X3,X1))=>v2_tex_2(k9_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 3.06/3.34  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.06/3.34  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.06/3.34  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.06/3.34  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.06/3.34  fof(t28_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_tarski(X3,X2)&v2_tex_2(X2,X1))=>v2_tex_2(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 3.06/3.34  fof(c_0_9, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(X26))|k9_subset_1(X26,X27,X28)=k3_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 3.06/3.34  fof(c_0_10, plain, ![X29, X30]:k1_setfam_1(k2_tarski(X29,X30))=k3_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 3.06/3.34  fof(c_0_11, plain, ![X24, X25]:k2_enumset1(X24,X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 3.06/3.34  fof(c_0_12, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X2,X1)|v2_tex_2(X3,X1))=>v2_tex_2(k9_subset_1(u1_struct_0(X1),X2,X3),X1)))))), inference(assume_negation,[status(cth)],[t29_tex_2])).
% 3.06/3.34  fof(c_0_13, plain, ![X20, X21]:r1_tarski(k3_xboole_0(X20,X21),X20), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 3.06/3.34  cnf(c_0_14, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.06/3.34  cnf(c_0_15, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 3.06/3.34  cnf(c_0_16, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 3.06/3.34  fof(c_0_17, negated_conjecture, (l1_pre_topc(esk3_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((v2_tex_2(esk4_0,esk3_0)|v2_tex_2(esk5_0,esk3_0))&~v2_tex_2(k9_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_0),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 3.06/3.34  fof(c_0_18, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 3.06/3.34  cnf(c_0_19, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.06/3.34  cnf(c_0_20, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_enumset1(X3,X3,X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 3.06/3.34  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.06/3.34  fof(c_0_22, plain, ![X22, X23]:k2_tarski(X22,X23)=k2_tarski(X23,X22), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 3.06/3.34  fof(c_0_23, plain, ![X31, X32]:((~m1_subset_1(X31,k1_zfmisc_1(X32))|r1_tarski(X31,X32))&(~r1_tarski(X31,X32)|m1_subset_1(X31,k1_zfmisc_1(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 3.06/3.34  cnf(c_0_24, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.06/3.34  cnf(c_0_25, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.06/3.34  cnf(c_0_26, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.06/3.34  cnf(c_0_27, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_15]), c_0_16])).
% 3.06/3.34  cnf(c_0_28, negated_conjecture, (k1_setfam_1(k2_enumset1(X1,X1,X1,esk5_0))=k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 3.06/3.34  cnf(c_0_29, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.06/3.34  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.06/3.34  cnf(c_0_31, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 3.06/3.34  cnf(c_0_32, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_26, c_0_25])).
% 3.06/3.34  cnf(c_0_33, negated_conjecture, (r1_tarski(k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0),X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 3.06/3.34  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_16]), c_0_16])).
% 3.06/3.34  cnf(c_0_35, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 3.06/3.34  cnf(c_0_36, negated_conjecture, (r2_hidden(esk1_2(k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0),X2),X1)|r1_tarski(k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0),X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 3.06/3.34  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.06/3.34  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.06/3.34  cnf(c_0_39, negated_conjecture, (k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,X1))=k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0)), inference(spm,[status(thm)],[c_0_28, c_0_34])).
% 3.06/3.34  cnf(c_0_40, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k9_subset_1(X2,X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_35])).
% 3.06/3.34  fof(c_0_41, plain, ![X33, X34, X35]:(~l1_pre_topc(X33)|(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|(~r1_tarski(X35,X34)|~v2_tex_2(X34,X33)|v2_tex_2(X35,X33))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_tex_2])])])).
% 3.06/3.34  cnf(c_0_42, negated_conjecture, (r2_hidden(esk1_2(k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0),X2),X3)|r1_tarski(k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0),X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_26, c_0_36])).
% 3.06/3.34  cnf(c_0_43, negated_conjecture, (r1_tarski(esk4_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 3.06/3.34  cnf(c_0_44, negated_conjecture, (k9_subset_1(X1,esk5_0,X1)=k9_subset_1(u1_struct_0(esk3_0),X1,esk5_0)), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 3.06/3.34  cnf(c_0_45, negated_conjecture, (k9_subset_1(u1_struct_0(esk3_0),X1,esk4_0)=k1_setfam_1(k2_enumset1(X1,X1,X1,esk4_0))), inference(spm,[status(thm)],[c_0_20, c_0_38])).
% 3.06/3.34  cnf(c_0_46, plain, (v2_tex_2(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X3,X2)|~v2_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 3.06/3.34  cnf(c_0_47, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.06/3.34  cnf(c_0_48, negated_conjecture, (r2_hidden(esk1_2(k9_subset_1(esk4_0,esk5_0,esk4_0),X1),u1_struct_0(esk3_0))|r1_tarski(k9_subset_1(esk4_0,esk5_0,esk4_0),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_44])).
% 3.06/3.34  cnf(c_0_49, negated_conjecture, (k9_subset_1(u1_struct_0(esk3_0),esk5_0,esk4_0)=k9_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_39, c_0_45])).
% 3.06/3.34  cnf(c_0_50, negated_conjecture, (k9_subset_1(u1_struct_0(esk3_0),X1,esk4_0)=k9_subset_1(esk4_0,X1,esk4_0)), inference(rw,[status(thm)],[c_0_45, c_0_40])).
% 3.06/3.34  cnf(c_0_51, negated_conjecture, (v2_tex_2(X1,esk3_0)|~v2_tex_2(X2,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 3.06/3.34  cnf(c_0_52, negated_conjecture, (v2_tex_2(esk4_0,esk3_0)|v2_tex_2(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.06/3.34  cnf(c_0_53, negated_conjecture, (r1_tarski(k9_subset_1(esk4_0,esk5_0,esk4_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_24, c_0_48])).
% 3.06/3.34  cnf(c_0_54, negated_conjecture, (~v2_tex_2(k9_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.06/3.34  cnf(c_0_55, negated_conjecture, (k9_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_0)=k9_subset_1(esk4_0,esk5_0,esk4_0)), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 3.06/3.34  cnf(c_0_56, negated_conjecture, (v2_tex_2(esk4_0,esk3_0)|v2_tex_2(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_21])])).
% 3.06/3.34  cnf(c_0_57, negated_conjecture, (m1_subset_1(k9_subset_1(esk4_0,esk5_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_30, c_0_53])).
% 3.06/3.34  cnf(c_0_58, plain, (r1_tarski(k9_subset_1(X1,X2,X1),X2)), inference(rw,[status(thm)],[c_0_27, c_0_40])).
% 3.06/3.34  cnf(c_0_59, negated_conjecture, (~v2_tex_2(k9_subset_1(esk4_0,esk5_0,esk4_0),esk3_0)), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 3.06/3.34  cnf(c_0_60, negated_conjecture, (v2_tex_2(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])]), c_0_59])).
% 3.06/3.34  cnf(c_0_61, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X2)), inference(spm,[status(thm)],[c_0_27, c_0_34])).
% 3.06/3.34  cnf(c_0_62, negated_conjecture, (v2_tex_2(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_60]), c_0_38])])).
% 3.06/3.34  cnf(c_0_63, plain, (r1_tarski(k9_subset_1(X1,X2,X1),X1)), inference(rw,[status(thm)],[c_0_61, c_0_40])).
% 3.06/3.34  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_57]), c_0_63])]), c_0_59]), ['proof']).
% 3.06/3.34  # SZS output end CNFRefutation
% 3.06/3.34  # Proof object total steps             : 65
% 3.06/3.34  # Proof object clause steps            : 46
% 3.06/3.34  # Proof object formula steps           : 19
% 3.06/3.34  # Proof object conjectures             : 28
% 3.06/3.34  # Proof object clause conjectures      : 25
% 3.06/3.34  # Proof object formula conjectures     : 3
% 3.06/3.34  # Proof object initial clauses used    : 16
% 3.06/3.34  # Proof object initial formulas used   : 9
% 3.06/3.34  # Proof object generating inferences   : 21
% 3.06/3.34  # Proof object simplifying inferences  : 24
% 3.06/3.34  # Training examples: 0 positive, 0 negative
% 3.06/3.34  # Parsed axioms                        : 10
% 3.06/3.34  # Removed by relevancy pruning/SinE    : 0
% 3.06/3.34  # Initial clauses                      : 22
% 3.06/3.34  # Removed in clause preprocessing      : 2
% 3.06/3.34  # Initial clauses in saturation        : 20
% 3.06/3.34  # Processed clauses                    : 7345
% 3.06/3.34  # ...of these trivial                  : 552
% 3.06/3.34  # ...subsumed                          : 4652
% 3.06/3.34  # ...remaining for further processing  : 2141
% 3.06/3.34  # Other redundant clauses eliminated   : 345
% 3.06/3.34  # Clauses deleted for lack of memory   : 0
% 3.06/3.34  # Backward-subsumed                    : 152
% 3.06/3.34  # Backward-rewritten                   : 482
% 3.06/3.34  # Generated clauses                    : 334205
% 3.06/3.34  # ...of the previous two non-trivial   : 316868
% 3.06/3.34  # Contextual simplify-reflections      : 22
% 3.06/3.34  # Paramodulations                      : 333495
% 3.06/3.34  # Factorizations                       : 322
% 3.06/3.34  # Equation resolutions                 : 388
% 3.06/3.34  # Propositional unsat checks           : 0
% 3.06/3.34  #    Propositional check models        : 0
% 3.06/3.34  #    Propositional check unsatisfiable : 0
% 3.06/3.34  #    Propositional clauses             : 0
% 3.06/3.34  #    Propositional clauses after purity: 0
% 3.06/3.34  #    Propositional unsat core size     : 0
% 3.06/3.34  #    Propositional preprocessing time  : 0.000
% 3.06/3.34  #    Propositional encoding time       : 0.000
% 3.06/3.34  #    Propositional solver time         : 0.000
% 3.06/3.34  #    Success case prop preproc time    : 0.000
% 3.06/3.34  #    Success case prop encoding time   : 0.000
% 3.06/3.34  #    Success case prop solver time     : 0.000
% 3.06/3.34  # Current number of processed clauses  : 1487
% 3.06/3.34  #    Positive orientable unit clauses  : 263
% 3.06/3.34  #    Positive unorientable unit clauses: 12
% 3.06/3.34  #    Negative unit clauses             : 1
% 3.06/3.34  #    Non-unit-clauses                  : 1211
% 3.06/3.34  # Current number of unprocessed clauses: 308185
% 3.06/3.34  # ...number of literals in the above   : 1657364
% 3.06/3.34  # Current number of archived formulas  : 0
% 3.06/3.34  # Current number of archived clauses   : 656
% 3.06/3.34  # Clause-clause subsumption calls (NU) : 694299
% 3.06/3.34  # Rec. Clause-clause subsumption calls : 219750
% 3.06/3.34  # Non-unit clause-clause subsumptions  : 4452
% 3.06/3.34  # Unit Clause-clause subsumption calls : 67239
% 3.06/3.34  # Rewrite failures with RHS unbound    : 0
% 3.06/3.34  # BW rewrite match attempts            : 9174
% 3.06/3.34  # BW rewrite match successes           : 335
% 3.06/3.34  # Condensation attempts                : 0
% 3.06/3.34  # Condensation successes               : 0
% 3.06/3.34  # Termbank termtop insertions          : 8355588
% 3.18/3.35  
% 3.18/3.35  # -------------------------------------------------
% 3.18/3.35  # User time                : 2.886 s
% 3.18/3.35  # System time              : 0.105 s
% 3.18/3.35  # Total time               : 2.991 s
% 3.18/3.35  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
