%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:57 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 131 expanded)
%              Number of clauses        :   24 (  50 expanded)
%              Number of leaves         :    8 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  152 ( 527 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   21 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_o_2_1_compts_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(o_2_1_compts_1(X1,X2),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_1_compts_1)).

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

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t35_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => v2_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(c_0_8,plain,(
    ! [X13,X14] :
      ( v2_struct_0(X13)
      | ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
      | m1_subset_1(o_2_1_compts_1(X13,X14),X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_o_2_1_compts_1])])])).

fof(c_0_9,plain,(
    ! [X5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X5)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ? [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
            & v3_tex_2(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t66_tex_2])).

cnf(c_0_11,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(o_2_1_compts_1(X1,X2),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,negated_conjecture,(
    ! [X21] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & v3_tdlat_3(esk2_0)
      & l1_pre_topc(esk2_0)
      & ( ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | ~ v3_tex_2(X21,esk2_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).

fof(c_0_14,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,X7)
      | v1_xboole_0(X7)
      | r2_hidden(X6,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(o_2_1_compts_1(X1,k1_xboole_0),k1_xboole_0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X15,X16] :
      ( v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ v1_xboole_0(X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | v2_tex_2(X16,X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_tex_2])])])])).

fof(c_0_20,plain,(
    ! [X11,X12] :
      ( ~ r2_hidden(X11,X12)
      | ~ r1_tarski(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(o_2_1_compts_1(esk2_0,k1_xboole_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])]),c_0_18])).

fof(c_0_23,plain,(
    ! [X4] : r1_tarski(k1_xboole_0,X4) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(o_2_1_compts_1(esk2_0,k1_xboole_0),k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X17,X18] :
      ( ( m1_subset_1(esk1_2(X17,X18),k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_tex_2(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ v3_tdlat_3(X17)
        | ~ l1_pre_topc(X17) )
      & ( r1_tarski(X18,esk1_2(X17,X18))
        | ~ v2_tex_2(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ v3_tdlat_3(X17)
        | ~ l1_pre_topc(X17) )
      & ( v3_tex_2(esk1_2(X17,X18),X17)
        | ~ v2_tex_2(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ v3_tdlat_3(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tex_2])])])])])])).

cnf(c_0_29,plain,
    ( v2_tex_2(k1_xboole_0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_31,plain,
    ( v3_tex_2(esk1_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( v2_tex_2(k1_xboole_0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_33,plain,
    ( v3_tex_2(esk1_2(X1,k1_xboole_0),X1)
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_12]),c_0_32])).

cnf(c_0_34,negated_conjecture,
    ( v3_tdlat_3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v3_tex_2(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( v3_tex_2(esk1_2(esk2_0,k1_xboole_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(esk1_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_12]),c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( ~ m1_subset_1(esk1_2(esk2_0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_34]),c_0_16]),c_0_17])]),c_0_18]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:11:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(dt_o_2_1_compts_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(o_2_1_compts_1(X1,X2),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_2_1_compts_1)).
% 0.13/0.37  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.37  fof(t66_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v3_tex_2(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 0.13/0.37  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.13/0.37  fof(t35_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v2_tex_2(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 0.13/0.37  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.13/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.37  fof(t65_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X2,X3)&v3_tex_2(X3,X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 0.13/0.37  fof(c_0_8, plain, ![X13, X14]:(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|m1_subset_1(o_2_1_compts_1(X13,X14),X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_o_2_1_compts_1])])])).
% 0.13/0.37  fof(c_0_9, plain, ![X5]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X5)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.37  fof(c_0_10, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v3_tex_2(X2,X1)))), inference(assume_negation,[status(cth)],[t66_tex_2])).
% 0.13/0.37  cnf(c_0_11, plain, (v2_struct_0(X1)|m1_subset_1(o_2_1_compts_1(X1,X2),X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_12, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  fof(c_0_13, negated_conjecture, ![X21]:((((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&v3_tdlat_3(esk2_0))&l1_pre_topc(esk2_0))&(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v3_tex_2(X21,esk2_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).
% 0.13/0.37  fof(c_0_14, plain, ![X6, X7]:(~m1_subset_1(X6,X7)|(v1_xboole_0(X7)|r2_hidden(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.13/0.37  cnf(c_0_15, plain, (v2_struct_0(X1)|m1_subset_1(o_2_1_compts_1(X1,k1_xboole_0),k1_xboole_0)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  fof(c_0_19, plain, ![X15, X16]:(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)|(~v1_xboole_0(X16)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|v2_tex_2(X16,X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_tex_2])])])])).
% 0.13/0.37  fof(c_0_20, plain, ![X11, X12]:(~r2_hidden(X11,X12)|~r1_tarski(X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.13/0.37  cnf(c_0_21, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (m1_subset_1(o_2_1_compts_1(esk2_0,k1_xboole_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])]), c_0_18])).
% 0.13/0.37  fof(c_0_23, plain, ![X4]:r1_tarski(k1_xboole_0,X4), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.37  cnf(c_0_24, plain, (v2_struct_0(X1)|v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_xboole_0(X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_25, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (r2_hidden(o_2_1_compts_1(esk2_0,k1_xboole_0),k1_xboole_0)|v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.37  cnf(c_0_27, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.37  fof(c_0_28, plain, ![X17, X18]:((m1_subset_1(esk1_2(X17,X18),k1_zfmisc_1(u1_struct_0(X17)))|~v2_tex_2(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~v3_tdlat_3(X17)|~l1_pre_topc(X17)))&((r1_tarski(X18,esk1_2(X17,X18))|~v2_tex_2(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~v3_tdlat_3(X17)|~l1_pre_topc(X17)))&(v3_tex_2(esk1_2(X17,X18),X17)|~v2_tex_2(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~v3_tdlat_3(X17)|~l1_pre_topc(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tex_2])])])])])])).
% 0.13/0.37  cnf(c_0_29, plain, (v2_tex_2(k1_xboole_0,X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_12])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (v1_xboole_0(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.13/0.37  cnf(c_0_31, plain, (v3_tex_2(esk1_2(X1,X2),X1)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.37  cnf(c_0_32, plain, (v2_tex_2(k1_xboole_0,X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30])])).
% 0.13/0.37  cnf(c_0_33, plain, (v3_tex_2(esk1_2(X1,k1_xboole_0),X1)|v2_struct_0(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_12]), c_0_32])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (v3_tdlat_3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_35, plain, (m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v3_tex_2(X1,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (v3_tex_2(esk1_2(esk2_0,k1_xboole_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_16]), c_0_17])]), c_0_18])).
% 0.13/0.37  cnf(c_0_38, plain, (v2_struct_0(X1)|m1_subset_1(esk1_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))|~v3_tdlat_3(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_12]), c_0_32])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (~m1_subset_1(esk1_2(esk2_0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.37  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_34]), c_0_16]), c_0_17])]), c_0_18]), c_0_39]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 41
% 0.13/0.37  # Proof object clause steps            : 24
% 0.13/0.37  # Proof object formula steps           : 17
% 0.13/0.37  # Proof object conjectures             : 14
% 0.13/0.37  # Proof object clause conjectures      : 11
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 13
% 0.13/0.37  # Proof object initial formulas used   : 8
% 0.13/0.37  # Proof object generating inferences   : 10
% 0.13/0.37  # Proof object simplifying inferences  : 18
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 9
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 15
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 15
% 0.13/0.37  # Processed clauses                    : 43
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 43
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 2
% 0.13/0.37  # Generated clauses                    : 15
% 0.13/0.37  # ...of the previous two non-trivial   : 14
% 0.13/0.37  # Contextual simplify-reflections      : 2
% 0.13/0.37  # Paramodulations                      : 15
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
% 0.13/0.37  # Current number of processed clauses  : 26
% 0.13/0.37  #    Positive orientable unit clauses  : 9
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 15
% 0.13/0.37  # Current number of unprocessed clauses: 0
% 0.13/0.37  # ...number of literals in the above   : 0
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 17
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 237
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 9
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.37  # Unit Clause-clause subsumption calls : 3
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 1
% 0.13/0.37  # BW rewrite match successes           : 1
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1841
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.027 s
% 0.13/0.37  # System time              : 0.006 s
% 0.13/0.37  # Total time               : 0.033 s
% 0.13/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
