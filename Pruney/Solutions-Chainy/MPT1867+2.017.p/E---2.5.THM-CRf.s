%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:50 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   45 (  86 expanded)
%              Number of clauses        :   25 (  35 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  147 ( 334 expanded)
%              Number of equality atoms :   19 (  26 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(idempotence_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(cc1_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_xboole_0(X2)
           => v3_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => v2_tex_2(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t35_tex_2])).

fof(c_0_11,plain,(
    ! [X6] :
      ( ~ v1_xboole_0(X6)
      | X6 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & v1_xboole_0(esk6_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & ~ v2_tex_2(esk6_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X34,X35,X36,X39] :
      ( ( m1_subset_1(esk3_3(X34,X35,X36),k1_zfmisc_1(u1_struct_0(X34)))
        | ~ r1_tarski(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ v2_tex_2(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_pre_topc(X34) )
      & ( v3_pre_topc(esk3_3(X34,X35,X36),X34)
        | ~ r1_tarski(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ v2_tex_2(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_pre_topc(X34) )
      & ( k9_subset_1(u1_struct_0(X34),X35,esk3_3(X34,X35,X36)) = X36
        | ~ r1_tarski(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ v2_tex_2(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_pre_topc(X34) )
      & ( m1_subset_1(esk4_2(X34,X35),k1_zfmisc_1(u1_struct_0(X34)))
        | v2_tex_2(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_pre_topc(X34) )
      & ( r1_tarski(esk4_2(X34,X35),X35)
        | v2_tex_2(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_pre_topc(X34) )
      & ( ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ v3_pre_topc(X39,X34)
        | k9_subset_1(u1_struct_0(X34),X35,X39) != esk4_2(X34,X35)
        | v2_tex_2(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).

fof(c_0_14,plain,(
    ! [X18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X18)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(X15))
      | k9_subset_1(X15,X16,X16) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k9_subset_1])])).

fof(c_0_18,plain,(
    ! [X13] : m1_subset_1(esk1_1(X13),X13) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_19,plain,
    ( r1_tarski(esk4_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_tex_2(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_23,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | m1_subset_1(X19,k1_zfmisc_1(X20)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_24,plain,(
    ! [X32,X33] :
      ( ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | ~ v1_xboole_0(X33)
      | v3_pre_topc(X33,X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tops_1])])])).

cnf(c_0_25,plain,
    ( k9_subset_1(X2,X3,X3) = X3
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_28,plain,
    ( v2_tex_2(k1_xboole_0,X1)
    | r1_tarski(esk4_2(X1,k1_xboole_0),k1_xboole_0)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_tex_2(k1_xboole_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,plain,
    ( v2_tex_2(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X2),X3,X1) != esk4_2(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,plain,
    ( k9_subset_1(X1,X2,X2) = X2 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_36,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk4_2(esk5_0,k1_xboole_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( v3_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_29]),c_0_33])])).

cnf(c_0_40,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_41,plain,
    ( v2_tex_2(X1,X2)
    | esk4_2(X2,X1) != X1
    | ~ v3_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( esk4_2(esk5_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_43,negated_conjecture,
    ( v3_pre_topc(k1_xboole_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_20]),c_0_40])])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_29]),c_0_20])]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 21:03:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.15/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.15/0.39  # and selection function PSelectComplexPreferEQ.
% 0.15/0.39  #
% 0.15/0.39  # Preprocessing time       : 0.028 s
% 0.15/0.39  # Presaturation interreduction done
% 0.15/0.39  
% 0.15/0.39  # Proof found!
% 0.15/0.39  # SZS status Theorem
% 0.15/0.39  # SZS output start CNFRefutation
% 0.15/0.39  fof(t35_tex_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v2_tex_2(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 0.15/0.39  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.15/0.39  fof(d5_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v3_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 0.15/0.39  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.15/0.39  fof(idempotence_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 0.15/0.39  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.15/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.15/0.39  fof(cc1_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_xboole_0(X2)=>v3_pre_topc(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tops_1)).
% 0.15/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.15/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.15/0.39  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v2_tex_2(X2,X1)))), inference(assume_negation,[status(cth)],[t35_tex_2])).
% 0.15/0.39  fof(c_0_11, plain, ![X6]:(~v1_xboole_0(X6)|X6=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.15/0.39  fof(c_0_12, negated_conjecture, (((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&((v1_xboole_0(esk6_0)&m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))))&~v2_tex_2(esk6_0,esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.15/0.39  fof(c_0_13, plain, ![X34, X35, X36, X39]:(((m1_subset_1(esk3_3(X34,X35,X36),k1_zfmisc_1(u1_struct_0(X34)))|~r1_tarski(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))|~v2_tex_2(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|~l1_pre_topc(X34))&((v3_pre_topc(esk3_3(X34,X35,X36),X34)|~r1_tarski(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))|~v2_tex_2(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|~l1_pre_topc(X34))&(k9_subset_1(u1_struct_0(X34),X35,esk3_3(X34,X35,X36))=X36|~r1_tarski(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34)))|~v2_tex_2(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|~l1_pre_topc(X34))))&((m1_subset_1(esk4_2(X34,X35),k1_zfmisc_1(u1_struct_0(X34)))|v2_tex_2(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|~l1_pre_topc(X34))&((r1_tarski(esk4_2(X34,X35),X35)|v2_tex_2(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|~l1_pre_topc(X34))&(~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X34)))|(~v3_pre_topc(X39,X34)|k9_subset_1(u1_struct_0(X34),X35,X39)!=esk4_2(X34,X35))|v2_tex_2(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|~l1_pre_topc(X34))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).
% 0.15/0.39  fof(c_0_14, plain, ![X18]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X18)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.15/0.39  cnf(c_0_15, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.39  cnf(c_0_16, negated_conjecture, (v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.39  fof(c_0_17, plain, ![X15, X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(X15))|k9_subset_1(X15,X16,X16)=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k9_subset_1])])).
% 0.15/0.39  fof(c_0_18, plain, ![X13]:m1_subset_1(esk1_1(X13),X13), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.15/0.39  cnf(c_0_19, plain, (r1_tarski(esk4_2(X1,X2),X2)|v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.39  cnf(c_0_20, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.39  cnf(c_0_21, negated_conjecture, (~v2_tex_2(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.39  cnf(c_0_22, negated_conjecture, (esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.15/0.39  fof(c_0_23, plain, ![X19, X20]:((~m1_subset_1(X19,k1_zfmisc_1(X20))|r1_tarski(X19,X20))&(~r1_tarski(X19,X20)|m1_subset_1(X19,k1_zfmisc_1(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.15/0.39  fof(c_0_24, plain, ![X32, X33]:(~v2_pre_topc(X32)|~l1_pre_topc(X32)|(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(~v1_xboole_0(X33)|v3_pre_topc(X33,X32)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tops_1])])])).
% 0.15/0.39  cnf(c_0_25, plain, (k9_subset_1(X2,X3,X3)=X3|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.15/0.39  cnf(c_0_26, plain, (m1_subset_1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.15/0.39  fof(c_0_27, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.15/0.39  cnf(c_0_28, plain, (v2_tex_2(k1_xboole_0,X1)|r1_tarski(esk4_2(X1,k1_xboole_0),k1_xboole_0)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.15/0.39  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.39  cnf(c_0_30, negated_conjecture, (~v2_tex_2(k1_xboole_0,esk5_0)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.15/0.39  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.15/0.39  cnf(c_0_32, plain, (v3_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.15/0.39  cnf(c_0_33, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.39  cnf(c_0_34, plain, (v2_tex_2(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|k9_subset_1(u1_struct_0(X2),X3,X1)!=esk4_2(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.39  cnf(c_0_35, plain, (k9_subset_1(X1,X2,X2)=X2), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.15/0.39  cnf(c_0_36, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.15/0.39  cnf(c_0_37, negated_conjecture, (r1_tarski(esk4_2(esk5_0,k1_xboole_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.15/0.39  cnf(c_0_38, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_31, c_0_20])).
% 0.15/0.39  cnf(c_0_39, negated_conjecture, (v3_pre_topc(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_29]), c_0_33])])).
% 0.15/0.39  cnf(c_0_40, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.15/0.39  cnf(c_0_41, plain, (v2_tex_2(X1,X2)|esk4_2(X2,X1)!=X1|~v3_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.15/0.39  cnf(c_0_42, negated_conjecture, (esk4_2(esk5_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.15/0.39  cnf(c_0_43, negated_conjecture, (v3_pre_topc(k1_xboole_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_20]), c_0_40])])).
% 0.15/0.39  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_29]), c_0_20])]), c_0_30]), ['proof']).
% 0.15/0.39  # SZS output end CNFRefutation
% 0.15/0.39  # Proof object total steps             : 45
% 0.15/0.39  # Proof object clause steps            : 25
% 0.15/0.39  # Proof object formula steps           : 20
% 0.15/0.39  # Proof object conjectures             : 14
% 0.15/0.39  # Proof object clause conjectures      : 11
% 0.15/0.39  # Proof object formula conjectures     : 3
% 0.15/0.39  # Proof object initial clauses used    : 14
% 0.15/0.39  # Proof object initial formulas used   : 10
% 0.15/0.39  # Proof object generating inferences   : 10
% 0.15/0.39  # Proof object simplifying inferences  : 13
% 0.15/0.39  # Training examples: 0 positive, 0 negative
% 0.15/0.39  # Parsed axioms                        : 15
% 0.15/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.39  # Initial clauses                      : 31
% 0.15/0.39  # Removed in clause preprocessing      : 0
% 0.15/0.39  # Initial clauses in saturation        : 31
% 0.15/0.39  # Processed clauses                    : 143
% 0.15/0.39  # ...of these trivial                  : 0
% 0.15/0.39  # ...subsumed                          : 25
% 0.15/0.39  # ...remaining for further processing  : 118
% 0.15/0.39  # Other redundant clauses eliminated   : 2
% 0.15/0.39  # Clauses deleted for lack of memory   : 0
% 0.15/0.39  # Backward-subsumed                    : 1
% 0.15/0.39  # Backward-rewritten                   : 4
% 0.15/0.39  # Generated clauses                    : 153
% 0.15/0.39  # ...of the previous two non-trivial   : 110
% 0.15/0.39  # Contextual simplify-reflections      : 0
% 0.15/0.39  # Paramodulations                      : 151
% 0.15/0.39  # Factorizations                       : 0
% 0.15/0.39  # Equation resolutions                 : 2
% 0.15/0.39  # Propositional unsat checks           : 0
% 0.15/0.39  #    Propositional check models        : 0
% 0.15/0.39  #    Propositional check unsatisfiable : 0
% 0.15/0.39  #    Propositional clauses             : 0
% 0.15/0.39  #    Propositional clauses after purity: 0
% 0.15/0.39  #    Propositional unsat core size     : 0
% 0.15/0.39  #    Propositional preprocessing time  : 0.000
% 0.15/0.39  #    Propositional encoding time       : 0.000
% 0.15/0.39  #    Propositional solver time         : 0.000
% 0.15/0.39  #    Success case prop preproc time    : 0.000
% 0.15/0.39  #    Success case prop encoding time   : 0.000
% 0.15/0.39  #    Success case prop solver time     : 0.000
% 0.15/0.39  # Current number of processed clauses  : 81
% 0.15/0.39  #    Positive orientable unit clauses  : 20
% 0.15/0.39  #    Positive unorientable unit clauses: 0
% 0.15/0.39  #    Negative unit clauses             : 3
% 0.15/0.39  #    Non-unit-clauses                  : 58
% 0.15/0.39  # Current number of unprocessed clauses: 23
% 0.15/0.39  # ...number of literals in the above   : 68
% 0.15/0.39  # Current number of archived formulas  : 0
% 0.15/0.39  # Current number of archived clauses   : 35
% 0.15/0.39  # Clause-clause subsumption calls (NU) : 421
% 0.15/0.39  # Rec. Clause-clause subsumption calls : 241
% 0.15/0.39  # Non-unit clause-clause subsumptions  : 12
% 0.15/0.39  # Unit Clause-clause subsumption calls : 21
% 0.15/0.39  # Rewrite failures with RHS unbound    : 0
% 0.15/0.39  # BW rewrite match attempts            : 7
% 0.15/0.39  # BW rewrite match successes           : 3
% 0.15/0.39  # Condensation attempts                : 0
% 0.15/0.39  # Condensation successes               : 0
% 0.15/0.39  # Termbank termtop insertions          : 4304
% 0.15/0.39  
% 0.15/0.39  # -------------------------------------------------
% 0.15/0.39  # User time                : 0.033 s
% 0.15/0.39  # System time              : 0.005 s
% 0.15/0.39  # Total time               : 0.038 s
% 0.15/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
