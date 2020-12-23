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
% DateTime   : Thu Dec  3 11:20:58 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 123 expanded)
%              Number of clauses        :   21 (  46 expanded)
%              Number of leaves         :    6 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :  183 ( 625 expanded)
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

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_6,plain,(
    ! [X12,X13,X14,X15] :
      ( ( ~ v2_tex_2(X13,X12)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r2_hidden(X14,X13)
        | ~ r2_hidden(X15,X13)
        | X14 = X15
        | r1_xboole_0(k2_pre_topc(X12,k6_domain_1(u1_struct_0(X12),X14)),k2_pre_topc(X12,k6_domain_1(u1_struct_0(X12),X15)))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ v3_tdlat_3(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk1_2(X12,X13),u1_struct_0(X12))
        | v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ v3_tdlat_3(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk2_2(X12,X13),u1_struct_0(X12))
        | v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ v3_tdlat_3(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk1_2(X12,X13),X13)
        | v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ v3_tdlat_3(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk2_2(X12,X13),X13)
        | v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ v3_tdlat_3(X12)
        | ~ l1_pre_topc(X12) )
      & ( esk1_2(X12,X13) != esk2_2(X12,X13)
        | v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ v3_tdlat_3(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r1_xboole_0(k2_pre_topc(X12,k6_domain_1(u1_struct_0(X12),esk1_2(X12,X13))),k2_pre_topc(X12,k6_domain_1(u1_struct_0(X12),esk2_2(X12,X13))))
        | v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ v3_tdlat_3(X12)
        | ~ l1_pre_topc(X12) ) ) ),
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
    ! [X9,X10,X11] :
      ( ~ r2_hidden(X9,X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X11))
      | ~ v1_xboole_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
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
    ! [X22] :
      ( ~ v2_struct_0(esk4_0)
      & v2_pre_topc(esk4_0)
      & v3_tdlat_3(esk4_0)
      & l1_pre_topc(esk4_0)
      & ( ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | ~ v3_tex_2(X22,esk4_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( v2_tex_2(k1_xboole_0,X1)
    | v2_struct_0(X1)
    | r2_hidden(esk1_2(X1,k1_xboole_0),k1_xboole_0)
    | ~ l1_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v3_tdlat_3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X18,X19] :
      ( ( m1_subset_1(esk3_2(X18,X19),k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v2_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ v3_tdlat_3(X18)
        | ~ l1_pre_topc(X18) )
      & ( r1_tarski(X19,esk3_2(X18,X19))
        | ~ v2_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ v3_tdlat_3(X18)
        | ~ l1_pre_topc(X18) )
      & ( v3_tex_2(esk3_2(X18,X19),X18)
        | ~ v2_tex_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ v3_tdlat_3(X18)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tex_2])])])])])])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( v2_tex_2(k1_xboole_0,esk4_0)
    | r2_hidden(esk1_2(esk4_0,k1_xboole_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( v2_tex_2(k1_xboole_0,esk4_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_25,plain,
    ( v3_tex_2(esk3_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(esk3_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( v2_tex_2(k1_xboole_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( v3_tex_2(esk3_2(X1,k1_xboole_0),X1)
    | v2_struct_0(X1)
    | ~ v2_tex_2(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v3_tex_2(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk3_2(esk4_0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( v3_tex_2(esk3_2(esk4_0,k1_xboole_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_27]),c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S2i
% 0.19/0.37  # and selection function SelectGrCQArEqFirst.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t59_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r2_hidden(X4,X2))=>(X3=X4|r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X4)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tex_2)).
% 0.19/0.37  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.37  fof(t66_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v3_tex_2(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 0.19/0.37  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.37  fof(t65_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X2,X3)&v3_tex_2(X3,X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 0.19/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.37  fof(c_0_6, plain, ![X12, X13, X14, X15]:((~v2_tex_2(X13,X12)|(~m1_subset_1(X14,u1_struct_0(X12))|(~m1_subset_1(X15,u1_struct_0(X12))|(~r2_hidden(X14,X13)|~r2_hidden(X15,X13)|(X14=X15|r1_xboole_0(k2_pre_topc(X12,k6_domain_1(u1_struct_0(X12),X14)),k2_pre_topc(X12,k6_domain_1(u1_struct_0(X12),X15)))))))|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~v3_tdlat_3(X12)|~l1_pre_topc(X12)))&((m1_subset_1(esk1_2(X12,X13),u1_struct_0(X12))|v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~v3_tdlat_3(X12)|~l1_pre_topc(X12)))&((m1_subset_1(esk2_2(X12,X13),u1_struct_0(X12))|v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~v3_tdlat_3(X12)|~l1_pre_topc(X12)))&(((r2_hidden(esk1_2(X12,X13),X13)|v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~v3_tdlat_3(X12)|~l1_pre_topc(X12)))&(r2_hidden(esk2_2(X12,X13),X13)|v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~v3_tdlat_3(X12)|~l1_pre_topc(X12))))&((esk1_2(X12,X13)!=esk2_2(X12,X13)|v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~v3_tdlat_3(X12)|~l1_pre_topc(X12)))&(~r1_xboole_0(k2_pre_topc(X12,k6_domain_1(u1_struct_0(X12),esk1_2(X12,X13))),k2_pre_topc(X12,k6_domain_1(u1_struct_0(X12),esk2_2(X12,X13))))|v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~v3_tdlat_3(X12)|~l1_pre_topc(X12)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tex_2])])])])])])).
% 0.19/0.37  fof(c_0_7, plain, ![X5]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X5)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.37  fof(c_0_8, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v3_tex_2(X2,X1)))), inference(assume_negation,[status(cth)],[t66_tex_2])).
% 0.19/0.37  fof(c_0_9, plain, ![X9, X10, X11]:(~r2_hidden(X9,X10)|~m1_subset_1(X10,k1_zfmisc_1(X11))|~v1_xboole_0(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.37  cnf(c_0_10, plain, (r2_hidden(esk1_2(X1,X2),X2)|v2_tex_2(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_11, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  fof(c_0_12, negated_conjecture, ![X22]:((((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&v3_tdlat_3(esk4_0))&l1_pre_topc(esk4_0))&(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(esk4_0)))|~v3_tex_2(X22,esk4_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).
% 0.19/0.37  cnf(c_0_13, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_14, plain, (v2_tex_2(k1_xboole_0,X1)|v2_struct_0(X1)|r2_hidden(esk1_2(X1,k1_xboole_0),k1_xboole_0)|~l1_pre_topc(X1)|~v3_tdlat_3(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (v3_tdlat_3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  fof(c_0_19, plain, ![X18, X19]:((m1_subset_1(esk3_2(X18,X19),k1_zfmisc_1(u1_struct_0(X18)))|~v2_tex_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~v3_tdlat_3(X18)|~l1_pre_topc(X18)))&((r1_tarski(X19,esk3_2(X18,X19))|~v2_tex_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~v3_tdlat_3(X18)|~l1_pre_topc(X18)))&(v3_tex_2(esk3_2(X18,X19),X18)|~v2_tex_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~v3_tdlat_3(X18)|~l1_pre_topc(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tex_2])])])])])])).
% 0.19/0.37  cnf(c_0_20, plain, (~r2_hidden(X1,k1_xboole_0)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_13, c_0_11])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (v2_tex_2(k1_xboole_0,esk4_0)|r2_hidden(esk1_2(esk4_0,k1_xboole_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.19/0.37  cnf(c_0_22, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (v2_tex_2(k1_xboole_0,esk4_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.37  cnf(c_0_24, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.37  cnf(c_0_25, plain, (v3_tex_2(esk3_2(X1,X2),X1)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_26, plain, (v2_struct_0(X1)|m1_subset_1(esk3_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(k1_xboole_0,X1)|~l1_pre_topc(X1)|~v3_tdlat_3(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_22, c_0_11])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (v2_tex_2(k1_xboole_0,esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.37  cnf(c_0_28, plain, (v3_tex_2(esk3_2(X1,k1_xboole_0),X1)|v2_struct_0(X1)|~v2_tex_2(k1_xboole_0,X1)|~l1_pre_topc(X1)|~v3_tdlat_3(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_25, c_0_11])).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~v3_tex_2(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk3_2(esk4_0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (v3_tex_2(esk3_2(esk4_0,k1_xboole_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_27]), c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 33
% 0.19/0.37  # Proof object clause steps            : 21
% 0.19/0.37  # Proof object formula steps           : 12
% 0.19/0.37  # Proof object conjectures             : 14
% 0.19/0.37  # Proof object clause conjectures      : 11
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 11
% 0.19/0.37  # Proof object initial formulas used   : 6
% 0.19/0.37  # Proof object generating inferences   : 10
% 0.19/0.37  # Proof object simplifying inferences  : 16
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 7
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 19
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 19
% 0.19/0.37  # Processed clauses                    : 54
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 54
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 3
% 0.19/0.37  # Generated clauses                    : 33
% 0.19/0.37  # ...of the previous two non-trivial   : 24
% 0.19/0.37  # Contextual simplify-reflections      : 2
% 0.19/0.37  # Paramodulations                      : 33
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
% 0.19/0.37  # Current number of processed clauses  : 32
% 0.19/0.37  #    Positive orientable unit clauses  : 9
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 2
% 0.19/0.37  #    Non-unit-clauses                  : 21
% 0.19/0.37  # Current number of unprocessed clauses: 3
% 0.19/0.37  # ...number of literals in the above   : 21
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 22
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 309
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 6
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.19/0.37  # Unit Clause-clause subsumption calls : 50
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 1
% 0.19/0.37  # BW rewrite match successes           : 1
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 3132
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.028 s
% 0.19/0.37  # System time              : 0.006 s
% 0.19/0.37  # Total time               : 0.034 s
% 0.19/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
