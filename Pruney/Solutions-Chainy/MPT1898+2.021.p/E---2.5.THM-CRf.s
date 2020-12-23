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
% DateTime   : Thu Dec  3 11:20:57 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 148 expanded)
%              Number of clauses        :   21 (  47 expanded)
%              Number of leaves         :    8 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  200 ( 800 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   54 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tex_2)).

fof(rc2_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

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
    ! [X23] :
      ( ~ v2_struct_0(esk5_0)
      & v2_pre_topc(esk5_0)
      & v3_tdlat_3(esk5_0)
      & l1_pre_topc(esk5_0)
      & ( ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(esk5_0)))
        | ~ v3_tex_2(X23,esk5_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).

fof(c_0_10,plain,(
    ! [X19,X20] :
      ( ( m1_subset_1(esk4_2(X19,X20),k1_zfmisc_1(u1_struct_0(X19)))
        | ~ v2_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ v3_tdlat_3(X19)
        | ~ l1_pre_topc(X19) )
      & ( r1_tarski(X20,esk4_2(X19,X20))
        | ~ v2_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ v3_tdlat_3(X19)
        | ~ l1_pre_topc(X19) )
      & ( v3_tex_2(esk4_2(X19,X20),X19)
        | ~ v2_tex_2(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ v3_tdlat_3(X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tex_2])])])])])])).

cnf(c_0_11,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v3_tex_2(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( v3_tdlat_3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( ~ v3_tex_2(esk4_2(esk5_0,X1),esk5_0)
    | ~ v2_tex_2(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_18,plain,
    ( v3_tex_2(esk4_2(X1,X2),X1)
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
    ( ~ v2_tex_2(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
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
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | ~ v2_tex_2(k6_domain_1(u1_struct_0(esk5_0),X1),esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_25,plain,(
    ! [X13,X14,X15,X16] :
      ( ( ~ v2_tex_2(X14,X13)
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | ~ m1_subset_1(X16,u1_struct_0(X13))
        | ~ r2_hidden(X15,X14)
        | ~ r2_hidden(X16,X14)
        | X15 = X16
        | r1_xboole_0(k2_pre_topc(X13,k6_domain_1(u1_struct_0(X13),X15)),k2_pre_topc(X13,k6_domain_1(u1_struct_0(X13),X16)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ v3_tdlat_3(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk2_2(X13,X14),u1_struct_0(X13))
        | v2_tex_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ v3_tdlat_3(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk3_2(X13,X14),u1_struct_0(X13))
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
      & ( r2_hidden(esk3_2(X13,X14),X14)
        | v2_tex_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ v3_tdlat_3(X13)
        | ~ l1_pre_topc(X13) )
      & ( esk2_2(X13,X14) != esk3_2(X13,X14)
        | v2_tex_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ v3_tdlat_3(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ r1_xboole_0(k2_pre_topc(X13,k6_domain_1(u1_struct_0(X13),esk2_2(X13,X14))),k2_pre_topc(X13,k6_domain_1(u1_struct_0(X13),esk3_2(X13,X14))))
        | v2_tex_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ v3_tdlat_3(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tex_2])])])])])])).

cnf(c_0_26,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_28,plain,(
    ! [X5] :
      ( m1_subset_1(esk1_1(X5),k1_zfmisc_1(X5))
      & v1_xboole_0(esk1_1(X5)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).

fof(c_0_29,plain,(
    ! [X8] :
      ( v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | ~ v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_30,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_20])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_34,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_35,negated_conjecture,
    ( ~ l1_struct_0(esk5_0) ),
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
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:11:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___092_C01_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.14/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t66_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v3_tex_2(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tex_2)).
% 0.14/0.38  fof(t65_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X2,X3)&v3_tex_2(X3,X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 0.14/0.38  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.14/0.38  fof(t36_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 0.14/0.38  fof(t59_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r2_hidden(X4,X2))=>(X3=X4|r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X4)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tex_2)).
% 0.14/0.38  fof(rc2_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&v1_xboole_0(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 0.14/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.14/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.14/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v3_tex_2(X2,X1)))), inference(assume_negation,[status(cth)],[t66_tex_2])).
% 0.14/0.38  fof(c_0_9, negated_conjecture, ![X23]:((((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&v3_tdlat_3(esk5_0))&l1_pre_topc(esk5_0))&(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v3_tex_2(X23,esk5_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).
% 0.14/0.38  fof(c_0_10, plain, ![X19, X20]:((m1_subset_1(esk4_2(X19,X20),k1_zfmisc_1(u1_struct_0(X19)))|~v2_tex_2(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~v3_tdlat_3(X19)|~l1_pre_topc(X19)))&((r1_tarski(X20,esk4_2(X19,X20))|~v2_tex_2(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~v3_tdlat_3(X19)|~l1_pre_topc(X19)))&(v3_tex_2(esk4_2(X19,X20),X19)|~v2_tex_2(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~v3_tdlat_3(X19)|~l1_pre_topc(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tex_2])])])])])])).
% 0.14/0.38  cnf(c_0_11, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v3_tex_2(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_12, plain, (m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_13, negated_conjecture, (v3_tdlat_3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_14, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_15, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (~v3_tex_2(esk4_2(esk5_0,X1),esk5_0)|~v2_tex_2(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 0.14/0.38  cnf(c_0_18, plain, (v3_tex_2(esk4_2(X1,X2),X1)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  fof(c_0_19, plain, ![X9, X10]:(v1_xboole_0(X9)|~m1_subset_1(X10,X9)|m1_subset_1(k6_domain_1(X9,X10),k1_zfmisc_1(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.14/0.38  cnf(c_0_20, negated_conjecture, (~v2_tex_2(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 0.14/0.38  cnf(c_0_21, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.38  fof(c_0_22, plain, ![X11, X12]:(v2_struct_0(X11)|~v2_pre_topc(X11)|~l1_pre_topc(X11)|(~m1_subset_1(X12,u1_struct_0(X11))|v2_tex_2(k6_domain_1(u1_struct_0(X11),X12),X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))|~v2_tex_2(k6_domain_1(u1_struct_0(esk5_0),X1),esk5_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.38  cnf(c_0_24, plain, (v2_struct_0(X1)|v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  fof(c_0_25, plain, ![X13, X14, X15, X16]:((~v2_tex_2(X14,X13)|(~m1_subset_1(X15,u1_struct_0(X13))|(~m1_subset_1(X16,u1_struct_0(X13))|(~r2_hidden(X15,X14)|~r2_hidden(X16,X14)|(X15=X16|r1_xboole_0(k2_pre_topc(X13,k6_domain_1(u1_struct_0(X13),X15)),k2_pre_topc(X13,k6_domain_1(u1_struct_0(X13),X16)))))))|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~v3_tdlat_3(X13)|~l1_pre_topc(X13)))&((m1_subset_1(esk2_2(X13,X14),u1_struct_0(X13))|v2_tex_2(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~v3_tdlat_3(X13)|~l1_pre_topc(X13)))&((m1_subset_1(esk3_2(X13,X14),u1_struct_0(X13))|v2_tex_2(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~v3_tdlat_3(X13)|~l1_pre_topc(X13)))&(((r2_hidden(esk2_2(X13,X14),X14)|v2_tex_2(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~v3_tdlat_3(X13)|~l1_pre_topc(X13)))&(r2_hidden(esk3_2(X13,X14),X14)|v2_tex_2(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~v3_tdlat_3(X13)|~l1_pre_topc(X13))))&((esk2_2(X13,X14)!=esk3_2(X13,X14)|v2_tex_2(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~v3_tdlat_3(X13)|~l1_pre_topc(X13)))&(~r1_xboole_0(k2_pre_topc(X13,k6_domain_1(u1_struct_0(X13),esk2_2(X13,X14))),k2_pre_topc(X13,k6_domain_1(u1_struct_0(X13),esk3_2(X13,X14))))|v2_tex_2(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~v3_tdlat_3(X13)|~l1_pre_topc(X13)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tex_2])])])])])])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_14]), c_0_15])]), c_0_16])).
% 0.14/0.38  cnf(c_0_27, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v2_tex_2(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.38  fof(c_0_28, plain, ![X5]:(m1_subset_1(esk1_1(X5),k1_zfmisc_1(X5))&v1_xboole_0(esk1_1(X5))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).
% 0.14/0.38  fof(c_0_29, plain, ![X8]:(v2_struct_0(X8)|~l1_struct_0(X8)|~v1_xboole_0(u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_13]), c_0_14]), c_0_15])]), c_0_16]), c_0_20])).
% 0.14/0.38  cnf(c_0_31, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.38  cnf(c_0_32, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.14/0.38  fof(c_0_34, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_16])).
% 0.14/0.38  cnf(c_0_36, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_15])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 38
% 0.14/0.38  # Proof object clause steps            : 21
% 0.14/0.38  # Proof object formula steps           : 17
% 0.14/0.38  # Proof object conjectures             : 16
% 0.14/0.38  # Proof object clause conjectures      : 13
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 13
% 0.14/0.38  # Proof object initial formulas used   : 8
% 0.14/0.38  # Proof object generating inferences   : 8
% 0.14/0.38  # Proof object simplifying inferences  : 23
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 8
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 21
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 21
% 0.14/0.38  # Processed clauses                    : 55
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 2
% 0.14/0.38  # ...remaining for further processing  : 53
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 3
% 0.14/0.38  # Backward-rewritten                   : 2
% 0.14/0.38  # Generated clauses                    : 21
% 0.14/0.38  # ...of the previous two non-trivial   : 20
% 0.14/0.38  # Contextual simplify-reflections      : 1
% 0.14/0.38  # Paramodulations                      : 21
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 27
% 0.14/0.38  #    Positive orientable unit clauses  : 6
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 4
% 0.14/0.38  #    Non-unit-clauses                  : 17
% 0.14/0.38  # Current number of unprocessed clauses: 7
% 0.14/0.38  # ...number of literals in the above   : 53
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 26
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 524
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 35
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 6
% 0.14/0.38  # Unit Clause-clause subsumption calls : 27
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 1
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 3064
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.030 s
% 0.14/0.38  # System time              : 0.005 s
% 0.14/0.38  # Total time               : 0.036 s
% 0.14/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
