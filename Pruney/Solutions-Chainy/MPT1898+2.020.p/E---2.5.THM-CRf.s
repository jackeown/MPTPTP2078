%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:56 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 148 expanded)
%              Number of clauses        :   21 (  47 expanded)
%              Number of leaves         :    8 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  172 ( 772 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   23 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t66_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & v3_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(t36_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(t57_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v4_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = k6_domain_1(u1_struct_0(X1),X3) ) ) ) )
           => v2_tex_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tex_2)).

fof(rc1_subset_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
          & ~ v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_subset_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(c_0_9,negated_conjecture,(
    ! [X21] :
      ( ~ v2_struct_0(esk4_0)
      & v2_pre_topc(esk4_0)
      & v3_tdlat_3(esk4_0)
      & l1_pre_topc(esk4_0)
      & ( ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | ~ v3_tex_2(X21,esk4_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).

fof(c_0_10,plain,(
    ! [X17,X18] :
      ( ( m1_subset_1(esk3_2(X17,X18),k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_tex_2(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ v3_tdlat_3(X17)
        | ~ l1_pre_topc(X17) )
      & ( r1_tarski(X18,esk3_2(X17,X18))
        | ~ v2_tex_2(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ v3_tdlat_3(X17)
        | ~ l1_pre_topc(X17) )
      & ( v3_tex_2(esk3_2(X17,X18),X17)
        | ~ v2_tex_2(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ v3_tdlat_3(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tex_2])])])])])])).

cnf(c_0_11,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v3_tex_2(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( v3_tdlat_3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( ~ v3_tex_2(esk3_2(esk4_0,X1),esk4_0)
    | ~ v2_tex_2(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_18,plain,
    ( v3_tex_2(esk3_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_19,plain,(
    ! [X9,X10] :
      ( v1_xboole_0(X9)
      | ~ m1_subset_1(X10,X9)
      | m1_subset_1(k6_domain_1(X9,X10),k1_zfmisc_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_tex_2(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_22,plain,(
    ! [X11,X12] :
      ( v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | v2_tex_2(k6_domain_1(u1_struct_0(X11),X12),X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).

cnf(c_0_23,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v2_tex_2(k6_domain_1(u1_struct_0(esk4_0),X1),esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_25,plain,(
    ! [X13,X14,X16] :
      ( ( m1_subset_1(esk2_2(X13,X14),u1_struct_0(X13))
        | v2_tex_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ v3_tdlat_3(X13)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk2_2(X13,X14),X14)
        | v2_tex_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ v3_tdlat_3(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ v4_pre_topc(X16,X13)
        | k9_subset_1(u1_struct_0(X13),X14,X16) != k6_domain_1(u1_struct_0(X13),esk2_2(X13,X14))
        | v2_tex_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ v3_tdlat_3(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_tex_2])])])])])])).

cnf(c_0_26,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))
    | v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_28,plain,(
    ! [X5] :
      ( ( m1_subset_1(esk1_1(X5),k1_zfmisc_1(X5))
        | v1_xboole_0(X5) )
      & ( ~ v1_xboole_0(esk1_1(X5))
        | v1_xboole_0(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc1_subset_1])])])])])).

fof(c_0_29,plain,(
    ! [X8] :
      ( v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | ~ v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_30,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_20])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_34,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_35,negated_conjecture,
    ( ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_16])).

cnf(c_0_36,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_15])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t66_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v3_tex_2(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tex_2)).
% 0.19/0.37  fof(t65_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X2,X3)&v3_tex_2(X3,X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 0.19/0.37  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.19/0.37  fof(t36_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 0.19/0.37  fof(t57_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v4_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=k6_domain_1(u1_struct_0(X1),X3)))))))=>v2_tex_2(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_tex_2)).
% 0.19/0.37  fof(rc1_subset_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_subset_1)).
% 0.19/0.37  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.37  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.37  fof(c_0_8, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v3_tex_2(X2,X1)))), inference(assume_negation,[status(cth)],[t66_tex_2])).
% 0.19/0.37  fof(c_0_9, negated_conjecture, ![X21]:((((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&v3_tdlat_3(esk4_0))&l1_pre_topc(esk4_0))&(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(esk4_0)))|~v3_tex_2(X21,esk4_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).
% 0.19/0.37  fof(c_0_10, plain, ![X17, X18]:((m1_subset_1(esk3_2(X17,X18),k1_zfmisc_1(u1_struct_0(X17)))|~v2_tex_2(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~v3_tdlat_3(X17)|~l1_pre_topc(X17)))&((r1_tarski(X18,esk3_2(X17,X18))|~v2_tex_2(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~v3_tdlat_3(X17)|~l1_pre_topc(X17)))&(v3_tex_2(esk3_2(X17,X18),X17)|~v2_tex_2(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~v3_tdlat_3(X17)|~l1_pre_topc(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tex_2])])])])])])).
% 0.19/0.37  cnf(c_0_11, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~v3_tex_2(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_12, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_13, negated_conjecture, (v3_tdlat_3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (~v3_tex_2(esk3_2(esk4_0,X1),esk4_0)|~v2_tex_2(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 0.19/0.37  cnf(c_0_18, plain, (v3_tex_2(esk3_2(X1,X2),X1)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  fof(c_0_19, plain, ![X9, X10]:(v1_xboole_0(X9)|~m1_subset_1(X10,X9)|m1_subset_1(k6_domain_1(X9,X10),k1_zfmisc_1(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (~v2_tex_2(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 0.19/0.37  cnf(c_0_21, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  fof(c_0_22, plain, ![X11, X12]:(v2_struct_0(X11)|~v2_pre_topc(X11)|~l1_pre_topc(X11)|(~m1_subset_1(X12,u1_struct_0(X11))|v2_tex_2(k6_domain_1(u1_struct_0(X11),X12),X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~v2_tex_2(k6_domain_1(u1_struct_0(esk4_0),X1),esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.37  cnf(c_0_24, plain, (v2_struct_0(X1)|v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  fof(c_0_25, plain, ![X13, X14, X16]:((m1_subset_1(esk2_2(X13,X14),u1_struct_0(X13))|v2_tex_2(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~v3_tdlat_3(X13)|~l1_pre_topc(X13)))&((r2_hidden(esk2_2(X13,X14),X14)|v2_tex_2(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~v3_tdlat_3(X13)|~l1_pre_topc(X13)))&(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X13)))|(~v4_pre_topc(X16,X13)|k9_subset_1(u1_struct_0(X13),X14,X16)!=k6_domain_1(u1_struct_0(X13),esk2_2(X13,X14)))|v2_tex_2(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~v3_tdlat_3(X13)|~l1_pre_topc(X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_tex_2])])])])])])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_14]), c_0_15])]), c_0_16])).
% 0.19/0.37  cnf(c_0_27, plain, (m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))|v2_tex_2(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  fof(c_0_28, plain, ![X5]:((m1_subset_1(esk1_1(X5),k1_zfmisc_1(X5))|v1_xboole_0(X5))&(~v1_xboole_0(esk1_1(X5))|v1_xboole_0(X5))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc1_subset_1])])])])])).
% 0.19/0.37  fof(c_0_29, plain, ![X8]:(v2_struct_0(X8)|~l1_struct_0(X8)|~v1_xboole_0(u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_13]), c_0_14]), c_0_15])]), c_0_16]), c_0_20])).
% 0.19/0.37  cnf(c_0_31, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(X1))|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.37  cnf(c_0_32, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.37  fof(c_0_34, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_16])).
% 0.19/0.37  cnf(c_0_36, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_15])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 38
% 0.19/0.37  # Proof object clause steps            : 21
% 0.19/0.37  # Proof object formula steps           : 17
% 0.19/0.37  # Proof object conjectures             : 16
% 0.19/0.37  # Proof object clause conjectures      : 13
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 13
% 0.19/0.37  # Proof object initial formulas used   : 8
% 0.19/0.37  # Proof object generating inferences   : 8
% 0.19/0.37  # Proof object simplifying inferences  : 23
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 8
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 17
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 17
% 0.19/0.37  # Processed clauses                    : 28
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 1
% 0.19/0.37  # ...remaining for further processing  : 27
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 3
% 0.19/0.37  # Backward-rewritten                   : 4
% 0.19/0.37  # Generated clauses                    : 14
% 0.19/0.37  # ...of the previous two non-trivial   : 13
% 0.19/0.37  # Contextual simplify-reflections      : 1
% 0.19/0.37  # Paramodulations                      : 14
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 20
% 0.19/0.37  #    Positive orientable unit clauses  : 4
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 2
% 0.19/0.37  #    Non-unit-clauses                  : 14
% 0.19/0.37  # Current number of unprocessed clauses: 0
% 0.19/0.37  # ...number of literals in the above   : 0
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 7
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 106
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 28
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 5
% 0.19/0.37  # Unit Clause-clause subsumption calls : 12
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 1
% 0.19/0.37  # BW rewrite match successes           : 1
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 2054
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.031 s
% 0.19/0.37  # System time              : 0.002 s
% 0.19/0.37  # Total time               : 0.033 s
% 0.19/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
