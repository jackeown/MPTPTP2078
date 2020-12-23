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
% DateTime   : Thu Dec  3 11:19:52 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   48 (  89 expanded)
%              Number of clauses        :   26 (  36 expanded)
%              Number of leaves         :   11 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  139 ( 329 expanded)
%              Number of equality atoms :   22 (  32 expanded)
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

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(d6_tex_2,axiom,(
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
                       => ~ ( v4_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = X3 ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(idempotence_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(cc2_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_xboole_0(X2)
           => v4_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => v2_tex_2(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t35_tex_2])).

fof(c_0_12,plain,(
    ! [X7] :
      ( ~ v1_xboole_0(X7)
      | X7 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & v1_xboole_0(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & ~ v2_tex_2(esk5_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_15,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_16,plain,(
    ! [X22,X23,X24,X27] :
      ( ( m1_subset_1(esk2_3(X22,X23,X24),k1_zfmisc_1(u1_struct_0(X22)))
        | ~ r1_tarski(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v2_tex_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) )
      & ( v4_pre_topc(esk2_3(X22,X23,X24),X22)
        | ~ r1_tarski(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v2_tex_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) )
      & ( k9_subset_1(u1_struct_0(X22),X23,esk2_3(X22,X23,X24)) = X24
        | ~ r1_tarski(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v2_tex_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(esk3_2(X22,X23),k1_zfmisc_1(u1_struct_0(X22)))
        | v2_tex_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) )
      & ( r1_tarski(esk3_2(X22,X23),X23)
        | v2_tex_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) )
      & ( ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v4_pre_topc(X27,X22)
        | k9_subset_1(u1_struct_0(X22),X23,X27) != esk3_2(X22,X23)
        | v2_tex_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tex_2])])])])])).

fof(c_0_17,plain,(
    ! [X16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X16)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X13))
      | k9_subset_1(X13,X14,X14) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k9_subset_1])])).

fof(c_0_21,plain,(
    ! [X11] : m1_subset_1(esk1_1(X11),X11) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( r1_tarski(esk3_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_tex_2(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,plain,
    ( k9_subset_1(X2,X3,X3) = X3
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( v2_tex_2(k1_xboole_0,X1)
    | r1_tarski(esk3_2(X1,k1_xboole_0),k1_xboole_0)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_tex_2(k1_xboole_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_34,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_35,plain,
    ( v2_tex_2(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X2),X3,X1) != esk3_2(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,plain,
    ( k9_subset_1(X1,X2,X2) = X2 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk3_2(esk4_0,k1_xboole_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( v2_tex_2(X1,X2)
    | esk3_2(X2,X1) != X1
    | ~ v4_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( esk3_2(esk4_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

fof(c_0_42,plain,(
    ! [X20,X21] :
      ( ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | ~ v1_xboole_0(X21)
      | v4_pre_topc(X21,X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_pre_topc])])])).

cnf(c_0_43,negated_conjecture,
    ( ~ v4_pre_topc(k1_xboole_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_32]),c_0_25])]),c_0_33])).

cnf(c_0_44,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_46,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_32]),c_0_45]),c_0_25]),c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n012.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 19:38:37 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  # Version: 2.5pre002
% 0.11/0.34  # No SInE strategy applied
% 0.11/0.34  # Trying AutoSched0 for 299 seconds
% 0.11/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.11/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.11/0.37  #
% 0.11/0.37  # Preprocessing time       : 0.027 s
% 0.11/0.37  # Presaturation interreduction done
% 0.11/0.37  
% 0.11/0.37  # Proof found!
% 0.11/0.37  # SZS status Theorem
% 0.11/0.37  # SZS output start CNFRefutation
% 0.11/0.37  fof(t35_tex_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v2_tex_2(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 0.11/0.37  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.11/0.37  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.11/0.37  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.11/0.37  fof(d6_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v4_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 0.11/0.37  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.11/0.37  fof(idempotence_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 0.11/0.37  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.11/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.11/0.37  fof(cc2_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_xboole_0(X2)=>v4_pre_topc(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 0.11/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.11/0.37  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v2_tex_2(X2,X1)))), inference(assume_negation,[status(cth)],[t35_tex_2])).
% 0.11/0.37  fof(c_0_12, plain, ![X7]:(~v1_xboole_0(X7)|X7=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.11/0.37  fof(c_0_13, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&((v1_xboole_0(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))))&~v2_tex_2(esk5_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.11/0.37  fof(c_0_14, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.11/0.37  fof(c_0_15, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.11/0.37  fof(c_0_16, plain, ![X22, X23, X24, X27]:(((m1_subset_1(esk2_3(X22,X23,X24),k1_zfmisc_1(u1_struct_0(X22)))|~r1_tarski(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|~v2_tex_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22))&((v4_pre_topc(esk2_3(X22,X23,X24),X22)|~r1_tarski(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|~v2_tex_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22))&(k9_subset_1(u1_struct_0(X22),X23,esk2_3(X22,X23,X24))=X24|~r1_tarski(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|~v2_tex_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22))))&((m1_subset_1(esk3_2(X22,X23),k1_zfmisc_1(u1_struct_0(X22)))|v2_tex_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22))&((r1_tarski(esk3_2(X22,X23),X23)|v2_tex_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22))&(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X22)))|(~v4_pre_topc(X27,X22)|k9_subset_1(u1_struct_0(X22),X23,X27)!=esk3_2(X22,X23))|v2_tex_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tex_2])])])])])).
% 0.11/0.37  fof(c_0_17, plain, ![X16]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X16)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.11/0.37  cnf(c_0_18, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.37  cnf(c_0_19, negated_conjecture, (v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.11/0.37  fof(c_0_20, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(X13))|k9_subset_1(X13,X14,X14)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k9_subset_1])])).
% 0.11/0.37  fof(c_0_21, plain, ![X11]:m1_subset_1(esk1_1(X11),X11), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.11/0.37  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.37  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.37  cnf(c_0_24, plain, (r1_tarski(esk3_2(X1,X2),X2)|v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.11/0.37  cnf(c_0_25, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.11/0.37  cnf(c_0_26, negated_conjecture, (~v2_tex_2(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.11/0.37  cnf(c_0_27, negated_conjecture, (esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.11/0.37  cnf(c_0_28, plain, (k9_subset_1(X2,X3,X3)=X3|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.11/0.37  cnf(c_0_29, plain, (m1_subset_1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.11/0.37  cnf(c_0_30, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.11/0.37  cnf(c_0_31, plain, (v2_tex_2(k1_xboole_0,X1)|r1_tarski(esk3_2(X1,k1_xboole_0),k1_xboole_0)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.11/0.37  cnf(c_0_32, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.11/0.37  cnf(c_0_33, negated_conjecture, (~v2_tex_2(k1_xboole_0,esk4_0)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.11/0.37  fof(c_0_34, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.11/0.37  cnf(c_0_35, plain, (v2_tex_2(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v4_pre_topc(X1,X2)|k9_subset_1(u1_struct_0(X2),X3,X1)!=esk3_2(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.11/0.37  cnf(c_0_36, plain, (k9_subset_1(X1,X2,X2)=X2), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.11/0.37  cnf(c_0_37, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_22, c_0_30])).
% 0.11/0.37  cnf(c_0_38, negated_conjecture, (r1_tarski(esk3_2(esk4_0,k1_xboole_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.11/0.37  cnf(c_0_39, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.11/0.37  cnf(c_0_40, plain, (v2_tex_2(X1,X2)|esk3_2(X2,X1)!=X1|~v4_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.11/0.37  cnf(c_0_41, negated_conjecture, (esk3_2(esk4_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.11/0.37  fof(c_0_42, plain, ![X20, X21]:(~v2_pre_topc(X20)|~l1_pre_topc(X20)|(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|(~v1_xboole_0(X21)|v4_pre_topc(X21,X20)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_pre_topc])])])).
% 0.11/0.37  cnf(c_0_43, negated_conjecture, (~v4_pre_topc(k1_xboole_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_32]), c_0_25])]), c_0_33])).
% 0.11/0.37  cnf(c_0_44, plain, (v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.11/0.37  cnf(c_0_45, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.11/0.37  cnf(c_0_46, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.11/0.37  cnf(c_0_47, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_32]), c_0_45]), c_0_25]), c_0_46])]), ['proof']).
% 0.11/0.37  # SZS output end CNFRefutation
% 0.11/0.37  # Proof object total steps             : 48
% 0.11/0.37  # Proof object clause steps            : 26
% 0.11/0.37  # Proof object formula steps           : 22
% 0.11/0.37  # Proof object conjectures             : 13
% 0.11/0.37  # Proof object clause conjectures      : 10
% 0.11/0.37  # Proof object formula conjectures     : 3
% 0.11/0.37  # Proof object initial clauses used    : 15
% 0.11/0.37  # Proof object initial formulas used   : 11
% 0.11/0.37  # Proof object generating inferences   : 10
% 0.11/0.37  # Proof object simplifying inferences  : 13
% 0.11/0.37  # Training examples: 0 positive, 0 negative
% 0.11/0.37  # Parsed axioms                        : 12
% 0.11/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.37  # Initial clauses                      : 22
% 0.11/0.37  # Removed in clause preprocessing      : 0
% 0.11/0.37  # Initial clauses in saturation        : 22
% 0.11/0.37  # Processed clauses                    : 64
% 0.11/0.37  # ...of these trivial                  : 0
% 0.11/0.37  # ...subsumed                          : 3
% 0.11/0.37  # ...remaining for further processing  : 61
% 0.11/0.37  # Other redundant clauses eliminated   : 0
% 0.11/0.37  # Clauses deleted for lack of memory   : 0
% 0.11/0.37  # Backward-subsumed                    : 0
% 0.11/0.37  # Backward-rewritten                   : 5
% 0.11/0.37  # Generated clauses                    : 31
% 0.11/0.37  # ...of the previous two non-trivial   : 29
% 0.11/0.37  # Contextual simplify-reflections      : 0
% 0.11/0.37  # Paramodulations                      : 31
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
% 0.11/0.37  # Current number of processed clauses  : 34
% 0.11/0.37  #    Positive orientable unit clauses  : 9
% 0.11/0.37  #    Positive unorientable unit clauses: 1
% 0.11/0.37  #    Negative unit clauses             : 3
% 0.11/0.37  #    Non-unit-clauses                  : 21
% 0.11/0.37  # Current number of unprocessed clauses: 7
% 0.11/0.37  # ...number of literals in the above   : 32
% 0.11/0.37  # Current number of archived formulas  : 0
% 0.11/0.37  # Current number of archived clauses   : 27
% 0.11/0.37  # Clause-clause subsumption calls (NU) : 290
% 0.11/0.37  # Rec. Clause-clause subsumption calls : 56
% 0.11/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.11/0.37  # Unit Clause-clause subsumption calls : 23
% 0.11/0.37  # Rewrite failures with RHS unbound    : 0
% 0.11/0.37  # BW rewrite match attempts            : 8
% 0.11/0.37  # BW rewrite match successes           : 7
% 0.11/0.37  # Condensation attempts                : 0
% 0.11/0.37  # Condensation successes               : 0
% 0.11/0.37  # Termbank termtop insertions          : 2384
% 0.11/0.37  
% 0.11/0.37  # -------------------------------------------------
% 0.11/0.37  # User time                : 0.032 s
% 0.11/0.37  # System time              : 0.002 s
% 0.11/0.37  # Total time               : 0.034 s
% 0.11/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
