%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:48 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 213 expanded)
%              Number of clauses        :   34 (  88 expanded)
%              Number of leaves         :   12 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :  155 ( 824 expanded)
%              Number of equality atoms :   31 (  86 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t35_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => v2_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(d5_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ~ ( r1_tarski(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v3_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = X3 ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(cc1_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_xboole_0(X2)
           => v3_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => v2_tex_2(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t35_tex_2])).

fof(c_0_13,plain,(
    ! [X7] :
      ( ~ v1_xboole_0(X7)
      | X7 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & v1_xboole_0(esk4_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ~ v2_tex_2(esk4_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X26,X27,X28,X31] :
      ( ( m1_subset_1(esk1_3(X26,X27,X28),k1_zfmisc_1(u1_struct_0(X26)))
        | ~ r1_tarski(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v2_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( v3_pre_topc(esk1_3(X26,X27,X28),X26)
        | ~ r1_tarski(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v2_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( k9_subset_1(u1_struct_0(X26),X27,esk1_3(X26,X27,X28)) = X28
        | ~ r1_tarski(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v2_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( m1_subset_1(esk2_2(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))
        | v2_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( r1_tarski(esk2_2(X26,X27),X27)
        | v2_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) )
      & ( ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v3_pre_topc(X31,X26)
        | k9_subset_1(u1_struct_0(X26),X27,X31) != esk2_2(X26,X27)
        | v2_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X17))
      | k9_subset_1(X17,X18,X19) = k3_xboole_0(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_19,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k4_xboole_0(X12,X13)) = k3_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_22,plain,(
    ! [X20] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X20)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v2_tex_2(X1,esk3_0)
    | m1_subset_1(esk2_2(esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_tex_2(k1_xboole_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( r1_tarski(esk2_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_31,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_32,plain,(
    ! [X11] :
      ( ~ r1_tarski(X11,k1_xboole_0)
      | X11 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_33,plain,(
    ! [X8,X9] : r1_tarski(k4_xboole_0(X8,X9),X8) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_34,plain,(
    ! [X24,X25] :
      ( ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ v1_xboole_0(X25)
      | v3_pre_topc(X25,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tops_1])])])).

cnf(c_0_35,plain,
    ( k9_subset_1(X2,X3,X1) = k4_xboole_0(X3,k4_xboole_0(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk2_2(esk3_0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( v2_tex_2(X1,esk3_0)
    | r1_tarski(esk2_2(esk3_0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_21])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_41,plain,(
    ! [X10] : k4_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_42,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_44,plain,
    ( v2_tex_2(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X2),X3,X1) != esk2_2(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk3_0),X1,esk2_2(esk3_0,k1_xboole_0)) = k4_xboole_0(X1,k4_xboole_0(X1,esk2_2(esk3_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk2_2(esk3_0,k1_xboole_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_28]),c_0_29])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_26]),c_0_26])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( v3_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_21]),c_0_43])])).

cnf(c_0_51,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_52,negated_conjecture,
    ( v2_tex_2(X1,esk3_0)
    | k4_xboole_0(X1,k4_xboole_0(X1,esk2_2(esk3_0,k1_xboole_0))) != esk2_2(esk3_0,X1)
    | ~ v3_pre_topc(esk2_2(esk3_0,k1_xboole_0),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_21]),c_0_36])])).

cnf(c_0_53,negated_conjecture,
    ( esk2_2(esk3_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_46])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( v3_pre_topc(k1_xboole_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_28])])).

cnf(c_0_56,negated_conjecture,
    ( v2_tex_2(X1,esk3_0)
    | esk2_2(esk3_0,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_49]),c_0_54]),c_0_53]),c_0_55])])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_53]),c_0_28])]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:43:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S002A
% 0.13/0.37  # and selection function SelectNegativeLiterals.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t35_tex_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v2_tex_2(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 0.13/0.37  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.13/0.37  fof(d5_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v3_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 0.13/0.37  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.13/0.37  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.37  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.37  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.37  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.13/0.37  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.13/0.37  fof(cc1_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_xboole_0(X2)=>v3_pre_topc(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tops_1)).
% 0.13/0.37  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.13/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.37  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v2_tex_2(X2,X1)))), inference(assume_negation,[status(cth)],[t35_tex_2])).
% 0.13/0.37  fof(c_0_13, plain, ![X7]:(~v1_xboole_0(X7)|X7=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.13/0.37  fof(c_0_14, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((v1_xboole_0(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))))&~v2_tex_2(esk4_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.13/0.37  fof(c_0_15, plain, ![X26, X27, X28, X31]:(((m1_subset_1(esk1_3(X26,X27,X28),k1_zfmisc_1(u1_struct_0(X26)))|~r1_tarski(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|~v2_tex_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))&((v3_pre_topc(esk1_3(X26,X27,X28),X26)|~r1_tarski(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|~v2_tex_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))&(k9_subset_1(u1_struct_0(X26),X27,esk1_3(X26,X27,X28))=X28|~r1_tarski(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|~v2_tex_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))))&((m1_subset_1(esk2_2(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))|v2_tex_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))&((r1_tarski(esk2_2(X26,X27),X27)|v2_tex_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))&(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X26)))|(~v3_pre_topc(X31,X26)|k9_subset_1(u1_struct_0(X26),X27,X31)!=esk2_2(X26,X27))|v2_tex_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|~l1_pre_topc(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).
% 0.13/0.37  cnf(c_0_16, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  fof(c_0_18, plain, ![X17, X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(X17))|k9_subset_1(X17,X18,X19)=k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.13/0.37  fof(c_0_19, plain, ![X12, X13]:k4_xboole_0(X12,k4_xboole_0(X12,X13))=k3_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.37  cnf(c_0_20, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  fof(c_0_22, plain, ![X20]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X20)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (~v2_tex_2(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.37  cnf(c_0_25, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (v2_tex_2(X1,esk3_0)|m1_subset_1(esk2_2(esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.37  cnf(c_0_28, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (~v2_tex_2(k1_xboole_0,esk3_0)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.37  cnf(c_0_30, plain, (r1_tarski(esk2_2(X1,X2),X2)|v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  fof(c_0_31, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.37  fof(c_0_32, plain, ![X11]:(~r1_tarski(X11,k1_xboole_0)|X11=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.13/0.37  fof(c_0_33, plain, ![X8, X9]:r1_tarski(k4_xboole_0(X8,X9),X8), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.13/0.37  fof(c_0_34, plain, ![X24, X25]:(~v2_pre_topc(X24)|~l1_pre_topc(X24)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(~v1_xboole_0(X25)|v3_pre_topc(X25,X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tops_1])])])).
% 0.13/0.37  cnf(c_0_35, plain, (k9_subset_1(X2,X3,X1)=k4_xboole_0(X3,k4_xboole_0(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk2_2(esk3_0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (v2_tex_2(X1,esk3_0)|r1_tarski(esk2_2(esk3_0,X1),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_30, c_0_21])).
% 0.13/0.37  cnf(c_0_38, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.37  cnf(c_0_39, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.37  cnf(c_0_40, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.37  fof(c_0_41, plain, ![X10]:k4_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.13/0.37  cnf(c_0_42, plain, (v3_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.37  cnf(c_0_43, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_44, plain, (v2_tex_2(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|k9_subset_1(u1_struct_0(X2),X3,X1)!=esk2_2(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_45, negated_conjecture, (k9_subset_1(u1_struct_0(esk3_0),X1,esk2_2(esk3_0,k1_xboole_0))=k4_xboole_0(X1,k4_xboole_0(X1,esk2_2(esk3_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.37  cnf(c_0_46, negated_conjecture, (r1_tarski(esk2_2(esk3_0,k1_xboole_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_28]), c_0_29])).
% 0.13/0.37  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_26]), c_0_26])).
% 0.13/0.37  cnf(c_0_48, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.37  cnf(c_0_49, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.37  cnf(c_0_50, negated_conjecture, (v3_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_21]), c_0_43])])).
% 0.13/0.37  cnf(c_0_51, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.37  cnf(c_0_52, negated_conjecture, (v2_tex_2(X1,esk3_0)|k4_xboole_0(X1,k4_xboole_0(X1,esk2_2(esk3_0,k1_xboole_0)))!=esk2_2(esk3_0,X1)|~v3_pre_topc(esk2_2(esk3_0,k1_xboole_0),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_21]), c_0_36])])).
% 0.13/0.37  cnf(c_0_53, negated_conjecture, (esk2_2(esk3_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_46])).
% 0.13/0.37  cnf(c_0_54, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.13/0.37  cnf(c_0_55, negated_conjecture, (v3_pre_topc(k1_xboole_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_28])])).
% 0.13/0.37  cnf(c_0_56, negated_conjecture, (v2_tex_2(X1,esk3_0)|esk2_2(esk3_0,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_49]), c_0_54]), c_0_53]), c_0_55])])).
% 0.13/0.37  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_53]), c_0_28])]), c_0_29]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 58
% 0.13/0.37  # Proof object clause steps            : 34
% 0.13/0.37  # Proof object formula steps           : 24
% 0.13/0.37  # Proof object conjectures             : 20
% 0.13/0.37  # Proof object clause conjectures      : 17
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 17
% 0.13/0.37  # Proof object initial formulas used   : 12
% 0.13/0.37  # Proof object generating inferences   : 13
% 0.13/0.37  # Proof object simplifying inferences  : 23
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 14
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 24
% 0.13/0.37  # Removed in clause preprocessing      : 1
% 0.13/0.37  # Initial clauses in saturation        : 23
% 0.13/0.37  # Processed clauses                    : 72
% 0.13/0.37  # ...of these trivial                  : 5
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 67
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 9
% 0.13/0.37  # Generated clauses                    : 52
% 0.13/0.37  # ...of the previous two non-trivial   : 43
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 52
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 35
% 0.13/0.37  #    Positive orientable unit clauses  : 16
% 0.13/0.37  #    Positive unorientable unit clauses: 1
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 16
% 0.13/0.37  # Current number of unprocessed clauses: 17
% 0.13/0.37  # ...number of literals in the above   : 44
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 33
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 224
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 43
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 20
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 18
% 0.13/0.37  # BW rewrite match successes           : 2
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 2811
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.031 s
% 0.13/0.37  # System time              : 0.003 s
% 0.13/0.37  # Total time               : 0.035 s
% 0.13/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
