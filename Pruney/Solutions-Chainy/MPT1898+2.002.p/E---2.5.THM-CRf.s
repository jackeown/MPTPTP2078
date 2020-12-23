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
% DateTime   : Thu Dec  3 11:20:54 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 135 expanded)
%              Number of clauses        :   22 (  50 expanded)
%              Number of leaves         :    6 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :  191 ( 679 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   54 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,X2)
                        & r2_hidden(X4,X2) )
                     => ( X3 = X4
                        | r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X4))) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tex_2)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t66_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & v3_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(rc1_connsp_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_connsp_1)).

fof(t65_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ~ ( v2_tex_2(X2,X1)
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ~ ( r1_tarski(X2,X3)
                      & v3_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).

fof(c_0_6,plain,(
    ! [X16,X17,X18,X19] :
      ( ( ~ v2_tex_2(X17,X16)
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ r2_hidden(X18,X17)
        | ~ r2_hidden(X19,X17)
        | X18 = X19
        | r1_xboole_0(k2_pre_topc(X16,k6_domain_1(u1_struct_0(X16),X18)),k2_pre_topc(X16,k6_domain_1(u1_struct_0(X16),X19)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ v3_tdlat_3(X16)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk2_2(X16,X17),u1_struct_0(X16))
        | v2_tex_2(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ v3_tdlat_3(X16)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk3_2(X16,X17),u1_struct_0(X16))
        | v2_tex_2(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ v3_tdlat_3(X16)
        | ~ l1_pre_topc(X16) )
      & ( r2_hidden(esk2_2(X16,X17),X17)
        | v2_tex_2(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ v3_tdlat_3(X16)
        | ~ l1_pre_topc(X16) )
      & ( r2_hidden(esk3_2(X16,X17),X17)
        | v2_tex_2(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ v3_tdlat_3(X16)
        | ~ l1_pre_topc(X16) )
      & ( esk2_2(X16,X17) != esk3_2(X16,X17)
        | v2_tex_2(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ v3_tdlat_3(X16)
        | ~ l1_pre_topc(X16) )
      & ( ~ r1_xboole_0(k2_pre_topc(X16,k6_domain_1(u1_struct_0(X16),esk2_2(X16,X17))),k2_pre_topc(X16,k6_domain_1(u1_struct_0(X16),esk3_2(X16,X17))))
        | v2_tex_2(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ v3_tdlat_3(X16)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tex_2])])])])])])).

fof(c_0_7,plain,(
    ! [X5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X5)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ? [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
            & v3_tex_2(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t66_tex_2])).

fof(c_0_9,plain,(
    ! [X11,X12,X13] :
      ( ~ r2_hidden(X11,X12)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X13))
      | ~ v1_xboole_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_10,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,negated_conjecture,(
    ! [X26] :
      ( ~ v2_struct_0(esk5_0)
      & v2_pre_topc(esk5_0)
      & v3_tdlat_3(esk5_0)
      & l1_pre_topc(esk5_0)
      & ( ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(esk5_0)))
        | ~ v3_tex_2(X26,esk5_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( v2_tex_2(k1_xboole_0,X1)
    | v2_struct_0(X1)
    | r2_hidden(esk2_2(X1,k1_xboole_0),k1_xboole_0)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v3_tdlat_3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X14] :
      ( ( m1_subset_1(esk1_1(X14),k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( v1_xboole_0(esk1_1(X14))
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[rc1_connsp_1])])])])).

fof(c_0_20,plain,(
    ! [X22,X23] :
      ( ( m1_subset_1(esk4_2(X22,X23),k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v2_tex_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ v3_tdlat_3(X22)
        | ~ l1_pre_topc(X22) )
      & ( r1_tarski(X23,esk4_2(X22,X23))
        | ~ v2_tex_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ v3_tdlat_3(X22)
        | ~ l1_pre_topc(X22) )
      & ( v3_tex_2(esk4_2(X22,X23),X22)
        | ~ v2_tex_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ v3_tdlat_3(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tex_2])])])])])])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( v2_tex_2(k1_xboole_0,esk5_0)
    | r2_hidden(esk2_2(esk5_0,k1_xboole_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_23,plain,
    ( v1_xboole_0(esk1_1(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v2_tex_2(k1_xboole_0,esk5_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( v1_xboole_0(esk1_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_15])).

cnf(c_0_27,plain,
    ( v3_tex_2(esk4_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(esk4_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(k1_xboole_0,X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( v2_tex_2(k1_xboole_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( v3_tex_2(esk4_2(X1,k1_xboole_0),X1)
    | v2_struct_0(X1)
    | ~ v2_tex_2(k1_xboole_0,X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v3_tex_2(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk4_2(esk5_0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_16]),c_0_17]),c_0_15])]),c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( v3_tex_2(esk4_2(esk5_0,k1_xboole_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_29]),c_0_16]),c_0_17]),c_0_15])]),c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:52:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S2i
% 0.13/0.38  # and selection function SelectGrCQArEqFirst.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t59_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r2_hidden(X4,X2))=>(X3=X4|r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X4)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tex_2)).
% 0.13/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.38  fof(t66_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v3_tex_2(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 0.13/0.38  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.13/0.38  fof(rc1_connsp_1, axiom, ![X1]:(l1_pre_topc(X1)=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_connsp_1)).
% 0.13/0.38  fof(t65_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X2,X3)&v3_tex_2(X3,X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 0.13/0.38  fof(c_0_6, plain, ![X16, X17, X18, X19]:((~v2_tex_2(X17,X16)|(~m1_subset_1(X18,u1_struct_0(X16))|(~m1_subset_1(X19,u1_struct_0(X16))|(~r2_hidden(X18,X17)|~r2_hidden(X19,X17)|(X18=X19|r1_xboole_0(k2_pre_topc(X16,k6_domain_1(u1_struct_0(X16),X18)),k2_pre_topc(X16,k6_domain_1(u1_struct_0(X16),X19)))))))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~v3_tdlat_3(X16)|~l1_pre_topc(X16)))&((m1_subset_1(esk2_2(X16,X17),u1_struct_0(X16))|v2_tex_2(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~v3_tdlat_3(X16)|~l1_pre_topc(X16)))&((m1_subset_1(esk3_2(X16,X17),u1_struct_0(X16))|v2_tex_2(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~v3_tdlat_3(X16)|~l1_pre_topc(X16)))&(((r2_hidden(esk2_2(X16,X17),X17)|v2_tex_2(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~v3_tdlat_3(X16)|~l1_pre_topc(X16)))&(r2_hidden(esk3_2(X16,X17),X17)|v2_tex_2(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~v3_tdlat_3(X16)|~l1_pre_topc(X16))))&((esk2_2(X16,X17)!=esk3_2(X16,X17)|v2_tex_2(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~v3_tdlat_3(X16)|~l1_pre_topc(X16)))&(~r1_xboole_0(k2_pre_topc(X16,k6_domain_1(u1_struct_0(X16),esk2_2(X16,X17))),k2_pre_topc(X16,k6_domain_1(u1_struct_0(X16),esk3_2(X16,X17))))|v2_tex_2(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~v3_tdlat_3(X16)|~l1_pre_topc(X16)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tex_2])])])])])])).
% 0.13/0.38  fof(c_0_7, plain, ![X5]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X5)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v3_tex_2(X2,X1)))), inference(assume_negation,[status(cth)],[t66_tex_2])).
% 0.13/0.38  fof(c_0_9, plain, ![X11, X12, X13]:(~r2_hidden(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(X13))|~v1_xboole_0(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.13/0.38  cnf(c_0_10, plain, (r2_hidden(esk2_2(X1,X2),X2)|v2_tex_2(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_11, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  fof(c_0_12, negated_conjecture, ![X26]:((((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&v3_tdlat_3(esk5_0))&l1_pre_topc(esk5_0))&(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v3_tex_2(X26,esk5_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).
% 0.13/0.38  cnf(c_0_13, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_14, plain, (v2_tex_2(k1_xboole_0,X1)|v2_struct_0(X1)|r2_hidden(esk2_2(X1,k1_xboole_0),k1_xboole_0)|~v3_tdlat_3(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (v3_tdlat_3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  fof(c_0_19, plain, ![X14]:((m1_subset_1(esk1_1(X14),k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))&(v1_xboole_0(esk1_1(X14))|~l1_pre_topc(X14))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[rc1_connsp_1])])])])).
% 0.13/0.38  fof(c_0_20, plain, ![X22, X23]:((m1_subset_1(esk4_2(X22,X23),k1_zfmisc_1(u1_struct_0(X22)))|~v2_tex_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~v3_tdlat_3(X22)|~l1_pre_topc(X22)))&((r1_tarski(X23,esk4_2(X22,X23))|~v2_tex_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~v3_tdlat_3(X22)|~l1_pre_topc(X22)))&(v3_tex_2(esk4_2(X22,X23),X22)|~v2_tex_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~v3_tdlat_3(X22)|~l1_pre_topc(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tex_2])])])])])])).
% 0.13/0.38  cnf(c_0_21, plain, (~r2_hidden(X1,k1_xboole_0)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_13, c_0_11])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (v2_tex_2(k1_xboole_0,esk5_0)|r2_hidden(esk2_2(esk5_0,k1_xboole_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.13/0.38  cnf(c_0_23, plain, (v1_xboole_0(esk1_1(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_24, plain, (m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (v2_tex_2(k1_xboole_0,esk5_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (v1_xboole_0(esk1_1(esk5_0))), inference(spm,[status(thm)],[c_0_23, c_0_15])).
% 0.13/0.38  cnf(c_0_27, plain, (v3_tex_2(esk4_2(X1,X2),X1)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_28, plain, (v2_struct_0(X1)|m1_subset_1(esk4_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(k1_xboole_0,X1)|~v3_tdlat_3(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_24, c_0_11])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (v2_tex_2(k1_xboole_0,esk5_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.38  cnf(c_0_30, plain, (v3_tex_2(esk4_2(X1,k1_xboole_0),X1)|v2_struct_0(X1)|~v2_tex_2(k1_xboole_0,X1)|~v3_tdlat_3(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_27, c_0_11])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v3_tex_2(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk4_2(esk5_0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_16]), c_0_17]), c_0_15])]), c_0_18])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (v3_tex_2(esk4_2(esk5_0,k1_xboole_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_29]), c_0_16]), c_0_17]), c_0_15])]), c_0_18])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 35
% 0.13/0.38  # Proof object clause steps            : 22
% 0.13/0.38  # Proof object formula steps           : 13
% 0.13/0.38  # Proof object conjectures             : 15
% 0.13/0.38  # Proof object clause conjectures      : 12
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 11
% 0.13/0.38  # Proof object initial formulas used   : 6
% 0.13/0.38  # Proof object generating inferences   : 11
% 0.13/0.38  # Proof object simplifying inferences  : 16
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 8
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 21
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 21
% 0.13/0.38  # Processed clauses                    : 66
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 66
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 3
% 0.13/0.38  # Generated clauses                    : 43
% 0.13/0.38  # ...of the previous two non-trivial   : 41
% 0.13/0.38  # Contextual simplify-reflections      : 2
% 0.13/0.38  # Paramodulations                      : 43
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 42
% 0.13/0.38  #    Positive orientable unit clauses  : 11
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 28
% 0.13/0.38  # Current number of unprocessed clauses: 6
% 0.13/0.38  # ...number of literals in the above   : 38
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 24
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 405
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 31
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.38  # Unit Clause-clause subsumption calls : 68
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 2
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3258
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.027 s
% 0.13/0.38  # System time              : 0.007 s
% 0.13/0.38  # Total time               : 0.034 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
