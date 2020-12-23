%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:52 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   41 (  97 expanded)
%              Number of clauses        :   24 (  39 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  133 ( 371 expanded)
%              Number of equality atoms :   19 (  33 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

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

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(cc1_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_xboole_0(X2)
           => v3_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => v2_tex_2(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t35_tex_2])).

fof(c_0_9,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k1_xboole_0)
      | X8 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_10,plain,(
    ! [X6,X7] : r1_tarski(k3_xboole_0(X6,X7),X6) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_11,plain,(
    ! [X5] :
      ( ~ v1_xboole_0(X5)
      | X5 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & v1_xboole_0(esk4_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ~ v2_tex_2(esk4_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_13,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X9))
      | k9_subset_1(X9,X10,X11) = k3_xboole_0(X10,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X18,X19,X20,X23] :
      ( ( m1_subset_1(esk1_3(X18,X19,X20),k1_zfmisc_1(u1_struct_0(X18)))
        | ~ r1_tarski(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v2_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( v3_pre_topc(esk1_3(X18,X19,X20),X18)
        | ~ r1_tarski(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v2_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( k9_subset_1(u1_struct_0(X18),X19,esk1_3(X18,X19,X20)) = X20
        | ~ r1_tarski(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v2_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(esk2_2(X18,X19),k1_zfmisc_1(u1_struct_0(X18)))
        | v2_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( r1_tarski(esk2_2(X18,X19),X19)
        | v2_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) )
      & ( ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v3_pre_topc(X23,X18)
        | k9_subset_1(u1_struct_0(X18),X19,X23) != esk2_2(X18,X19)
        | v2_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).

fof(c_0_17,plain,(
    ! [X12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X12)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( r1_tarski(esk2_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( v2_tex_2(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X2),X3,X1) != esk2_2(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k9_subset_1(X1,k1_xboole_0,X2) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( v2_tex_2(k1_xboole_0,X1)
    | r1_tarski(esk2_2(X1,k1_xboole_0),k1_xboole_0)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_tex_2(k1_xboole_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( v2_tex_2(k1_xboole_0,X1)
    | esk2_2(X1,k1_xboole_0) != k1_xboole_0
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_23])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk2_2(esk3_0,k1_xboole_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_33,plain,
    ( v2_tex_2(k1_xboole_0,X1)
    | esk2_2(X1,k1_xboole_0) != k1_xboole_0
    | ~ v3_pre_topc(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( esk2_2(esk3_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_32])).

fof(c_0_35,plain,(
    ! [X16,X17] :
      ( ~ v2_pre_topc(X16)
      | ~ l1_pre_topc(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
      | ~ v1_xboole_0(X17)
      | v3_pre_topc(X17,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tops_1])])])).

cnf(c_0_36,negated_conjecture,
    ( ~ v3_pre_topc(k1_xboole_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_29])]),c_0_30])).

cnf(c_0_37,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_19,c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_29]),c_0_38]),c_0_23]),c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n014.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 11:56:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.027 s
% 0.18/0.36  # Presaturation interreduction done
% 0.18/0.36  
% 0.18/0.36  # Proof found!
% 0.18/0.36  # SZS status Theorem
% 0.18/0.36  # SZS output start CNFRefutation
% 0.18/0.36  fof(t35_tex_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v2_tex_2(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 0.18/0.36  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.18/0.36  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.18/0.36  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.18/0.36  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.18/0.36  fof(d5_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v3_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 0.18/0.36  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.18/0.36  fof(cc1_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_xboole_0(X2)=>v3_pre_topc(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tops_1)).
% 0.18/0.36  fof(c_0_8, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v2_tex_2(X2,X1)))), inference(assume_negation,[status(cth)],[t35_tex_2])).
% 0.18/0.36  fof(c_0_9, plain, ![X8]:(~r1_tarski(X8,k1_xboole_0)|X8=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.18/0.36  fof(c_0_10, plain, ![X6, X7]:r1_tarski(k3_xboole_0(X6,X7),X6), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.18/0.36  fof(c_0_11, plain, ![X5]:(~v1_xboole_0(X5)|X5=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.18/0.36  fof(c_0_12, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((v1_xboole_0(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))))&~v2_tex_2(esk4_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.18/0.36  fof(c_0_13, plain, ![X9, X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(X9))|k9_subset_1(X9,X10,X11)=k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.18/0.36  cnf(c_0_14, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.36  cnf(c_0_15, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.36  fof(c_0_16, plain, ![X18, X19, X20, X23]:(((m1_subset_1(esk1_3(X18,X19,X20),k1_zfmisc_1(u1_struct_0(X18)))|~r1_tarski(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|~v2_tex_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))&((v3_pre_topc(esk1_3(X18,X19,X20),X18)|~r1_tarski(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|~v2_tex_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))&(k9_subset_1(u1_struct_0(X18),X19,esk1_3(X18,X19,X20))=X20|~r1_tarski(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|~v2_tex_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))))&((m1_subset_1(esk2_2(X18,X19),k1_zfmisc_1(u1_struct_0(X18)))|v2_tex_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))&((r1_tarski(esk2_2(X18,X19),X19)|v2_tex_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))&(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X18)))|(~v3_pre_topc(X23,X18)|k9_subset_1(u1_struct_0(X18),X19,X23)!=esk2_2(X18,X19))|v2_tex_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_pre_topc(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).
% 0.18/0.36  fof(c_0_17, plain, ![X12]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X12)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.18/0.36  cnf(c_0_18, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.36  cnf(c_0_19, negated_conjecture, (v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  cnf(c_0_20, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.36  cnf(c_0_21, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.18/0.36  cnf(c_0_22, plain, (r1_tarski(esk2_2(X1,X2),X2)|v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.36  cnf(c_0_23, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.36  cnf(c_0_24, negated_conjecture, (~v2_tex_2(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  cnf(c_0_25, negated_conjecture, (esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.18/0.36  cnf(c_0_26, plain, (v2_tex_2(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|k9_subset_1(u1_struct_0(X2),X3,X1)!=esk2_2(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.36  cnf(c_0_27, plain, (k9_subset_1(X1,k1_xboole_0,X2)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.18/0.36  cnf(c_0_28, plain, (v2_tex_2(k1_xboole_0,X1)|r1_tarski(esk2_2(X1,k1_xboole_0),k1_xboole_0)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.36  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  cnf(c_0_30, negated_conjecture, (~v2_tex_2(k1_xboole_0,esk3_0)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.36  cnf(c_0_31, plain, (v2_tex_2(k1_xboole_0,X1)|esk2_2(X1,k1_xboole_0)!=k1_xboole_0|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_23])])).
% 0.18/0.36  cnf(c_0_32, negated_conjecture, (r1_tarski(esk2_2(esk3_0,k1_xboole_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.18/0.36  cnf(c_0_33, plain, (v2_tex_2(k1_xboole_0,X1)|esk2_2(X1,k1_xboole_0)!=k1_xboole_0|~v3_pre_topc(k1_xboole_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_31, c_0_23])).
% 0.18/0.36  cnf(c_0_34, negated_conjecture, (esk2_2(esk3_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_14, c_0_32])).
% 0.18/0.36  fof(c_0_35, plain, ![X16, X17]:(~v2_pre_topc(X16)|~l1_pre_topc(X16)|(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(~v1_xboole_0(X17)|v3_pre_topc(X17,X16)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tops_1])])])).
% 0.18/0.36  cnf(c_0_36, negated_conjecture, (~v3_pre_topc(k1_xboole_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_29])]), c_0_30])).
% 0.18/0.36  cnf(c_0_37, plain, (v3_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.36  cnf(c_0_38, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  cnf(c_0_39, negated_conjecture, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_19, c_0_25])).
% 0.18/0.36  cnf(c_0_40, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_29]), c_0_38]), c_0_23]), c_0_39])]), ['proof']).
% 0.18/0.36  # SZS output end CNFRefutation
% 0.18/0.36  # Proof object total steps             : 41
% 0.18/0.36  # Proof object clause steps            : 24
% 0.18/0.36  # Proof object formula steps           : 17
% 0.18/0.36  # Proof object conjectures             : 14
% 0.18/0.36  # Proof object clause conjectures      : 11
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 12
% 0.18/0.36  # Proof object initial formulas used   : 8
% 0.18/0.36  # Proof object generating inferences   : 10
% 0.18/0.36  # Proof object simplifying inferences  : 13
% 0.18/0.36  # Training examples: 0 positive, 0 negative
% 0.18/0.36  # Parsed axioms                        : 9
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 19
% 0.18/0.36  # Removed in clause preprocessing      : 0
% 0.18/0.36  # Initial clauses in saturation        : 19
% 0.18/0.36  # Processed clauses                    : 59
% 0.18/0.36  # ...of these trivial                  : 1
% 0.18/0.36  # ...subsumed                          : 2
% 0.18/0.36  # ...remaining for further processing  : 56
% 0.18/0.36  # Other redundant clauses eliminated   : 0
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 0
% 0.18/0.36  # Backward-rewritten                   : 7
% 0.18/0.36  # Generated clauses                    : 35
% 0.18/0.36  # ...of the previous two non-trivial   : 33
% 0.18/0.36  # Contextual simplify-reflections      : 0
% 0.18/0.36  # Paramodulations                      : 35
% 0.18/0.36  # Factorizations                       : 0
% 0.18/0.36  # Equation resolutions                 : 0
% 0.18/0.36  # Propositional unsat checks           : 0
% 0.18/0.36  #    Propositional check models        : 0
% 0.18/0.36  #    Propositional check unsatisfiable : 0
% 0.18/0.36  #    Propositional clauses             : 0
% 0.18/0.36  #    Propositional clauses after purity: 0
% 0.18/0.36  #    Propositional unsat core size     : 0
% 0.18/0.36  #    Propositional preprocessing time  : 0.000
% 0.18/0.36  #    Propositional encoding time       : 0.000
% 0.18/0.36  #    Propositional solver time         : 0.000
% 0.18/0.36  #    Success case prop preproc time    : 0.000
% 0.18/0.36  #    Success case prop encoding time   : 0.000
% 0.18/0.36  #    Success case prop solver time     : 0.000
% 0.18/0.36  # Current number of processed clauses  : 30
% 0.18/0.36  #    Positive orientable unit clauses  : 9
% 0.18/0.36  #    Positive unorientable unit clauses: 0
% 0.18/0.36  #    Negative unit clauses             : 3
% 0.18/0.36  #    Non-unit-clauses                  : 18
% 0.18/0.36  # Current number of unprocessed clauses: 8
% 0.18/0.36  # ...number of literals in the above   : 51
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 26
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 365
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 58
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 2
% 0.18/0.36  # Unit Clause-clause subsumption calls : 18
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 2
% 0.18/0.36  # BW rewrite match successes           : 2
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 2369
% 0.18/0.36  
% 0.18/0.36  # -------------------------------------------------
% 0.18/0.36  # User time                : 0.029 s
% 0.18/0.36  # System time              : 0.004 s
% 0.18/0.36  # Total time               : 0.033 s
% 0.18/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
