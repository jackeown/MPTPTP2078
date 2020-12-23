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
% DateTime   : Thu Dec  3 11:20:44 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 482 expanded)
%              Number of clauses        :   24 ( 149 expanded)
%              Number of leaves         :    4 ( 119 expanded)
%              Depth                    :   10
%              Number of atoms          :  213 (4398 expanded)
%              Number of equality atoms :   17 ( 358 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   35 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ~ ( v3_tex_2(X2,X1)
              & ! [X3] :
                  ( ( ~ v2_struct_0(X3)
                    & v1_pre_topc(X3)
                    & m1_pre_topc(X3,X1) )
                 => ~ ( v4_tex_2(X3,X1)
                      & X2 = u1_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tex_2)).

fof(d7_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tex_2(X2,X1)
          <=> ( v2_tex_2(X2,X1)
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_tex_2(X3,X1)
                      & r1_tarski(X2,X3) )
                   => X2 = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(t34_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ~ ( v2_tex_2(X2,X1)
              & ! [X3] :
                  ( ( ~ v2_struct_0(X3)
                    & v1_pre_topc(X3)
                    & v1_tdlat_3(X3)
                    & m1_pre_topc(X3,X1) )
                 => X2 != u1_struct_0(X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

fof(d8_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v4_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v3_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ~ ( v3_tex_2(X2,X1)
                & ! [X3] :
                    ( ( ~ v2_struct_0(X3)
                      & v1_pre_topc(X3)
                      & m1_pre_topc(X3,X1) )
                   => ~ ( v4_tex_2(X3,X1)
                        & X2 = u1_struct_0(X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t53_tex_2])).

fof(c_0_5,plain,(
    ! [X4,X5,X6] :
      ( ( v2_tex_2(X5,X4)
        | ~ v3_tex_2(X5,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4) )
      & ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ v2_tex_2(X6,X4)
        | ~ r1_tarski(X5,X6)
        | X5 = X6
        | ~ v3_tex_2(X5,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4) )
      & ( m1_subset_1(esk1_2(X4,X5),k1_zfmisc_1(u1_struct_0(X4)))
        | ~ v2_tex_2(X5,X4)
        | v3_tex_2(X5,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4) )
      & ( v2_tex_2(esk1_2(X4,X5),X4)
        | ~ v2_tex_2(X5,X4)
        | v3_tex_2(X5,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4) )
      & ( r1_tarski(X5,esk1_2(X4,X5))
        | ~ v2_tex_2(X5,X4)
        | v3_tex_2(X5,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4) )
      & ( X5 != esk1_2(X4,X5)
        | ~ v2_tex_2(X5,X4)
        | v3_tex_2(X5,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ l1_pre_topc(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).

fof(c_0_6,negated_conjecture,(
    ! [X17] :
      ( ~ v2_struct_0(esk4_0)
      & v2_pre_topc(esk4_0)
      & l1_pre_topc(esk4_0)
      & ~ v1_xboole_0(esk5_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
      & v3_tex_2(esk5_0,esk4_0)
      & ( v2_struct_0(X17)
        | ~ v1_pre_topc(X17)
        | ~ m1_pre_topc(X17,esk4_0)
        | ~ v4_tex_2(X17,esk4_0)
        | esk5_0 != u1_struct_0(X17) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).

fof(c_0_7,plain,(
    ! [X12,X13] :
      ( ( ~ v2_struct_0(esk3_2(X12,X13))
        | ~ v2_tex_2(X13,X12)
        | v1_xboole_0(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( v1_pre_topc(esk3_2(X12,X13))
        | ~ v2_tex_2(X13,X12)
        | v1_xboole_0(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( v1_tdlat_3(esk3_2(X12,X13))
        | ~ v2_tex_2(X13,X12)
        | v1_xboole_0(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_pre_topc(esk3_2(X12,X13),X12)
        | ~ v2_tex_2(X13,X12)
        | v1_xboole_0(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( X13 = u1_struct_0(esk3_2(X12,X13))
        | ~ v2_tex_2(X13,X12)
        | v1_xboole_0(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).

cnf(c_0_8,plain,
    ( v2_tex_2(X1,X2)
    | ~ v3_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v3_tex_2(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( v1_pre_topc(esk3_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( v2_tex_2(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_15,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk3_2(X1,X2))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ v4_tex_2(X1,esk4_0)
    | esk5_0 != u1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( v1_pre_topc(esk3_2(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_9]),c_0_13]),c_0_14]),c_0_11])]),c_0_15]),c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk3_2(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_9]),c_0_13]),c_0_14]),c_0_11])]),c_0_15]),c_0_16])).

cnf(c_0_21,plain,
    ( X1 = u1_struct_0(esk3_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( u1_struct_0(esk3_2(esk4_0,esk5_0)) != esk5_0
    | ~ v4_tex_2(esk3_2(esk4_0,esk5_0),esk4_0)
    | ~ m1_pre_topc(esk3_2(esk4_0,esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( u1_struct_0(esk3_2(esk4_0,esk5_0)) = esk5_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_9]),c_0_13]),c_0_14]),c_0_11])]),c_0_15]),c_0_16])).

cnf(c_0_24,plain,
    ( m1_pre_topc(esk3_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_25,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v4_tex_2(X9,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | X10 != u1_struct_0(X9)
        | v3_tex_2(X10,X8)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ l1_pre_topc(X8) )
      & ( m1_subset_1(esk2_2(X8,X9),k1_zfmisc_1(u1_struct_0(X8)))
        | v4_tex_2(X9,X8)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ l1_pre_topc(X8) )
      & ( esk2_2(X8,X9) = u1_struct_0(X9)
        | v4_tex_2(X9,X8)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ l1_pre_topc(X8) )
      & ( ~ v3_tex_2(esk2_2(X8,X9),X8)
        | v4_tex_2(X9,X8)
        | ~ m1_pre_topc(X9,X8)
        | v2_struct_0(X8)
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_tex_2])])])])])])).

cnf(c_0_26,negated_conjecture,
    ( ~ v4_tex_2(esk3_2(esk4_0,esk5_0),esk4_0)
    | ~ m1_pre_topc(esk3_2(esk4_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23])])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk3_2(esk4_0,esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_9]),c_0_13]),c_0_14]),c_0_11])]),c_0_15]),c_0_16])).

cnf(c_0_28,plain,
    ( esk2_2(X1,X2) = u1_struct_0(X2)
    | v4_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( ~ v4_tex_2(esk3_2(esk4_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27])])).

cnf(c_0_30,plain,
    ( v4_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ v3_tex_2(esk2_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( esk2_2(esk4_0,esk3_2(esk4_0,esk5_0)) = esk5_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_27]),c_0_23]),c_0_11])]),c_0_16]),c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_27]),c_0_10]),c_0_11])]),c_0_29]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:26:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.029 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t53_tex_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~((v3_tex_2(X2,X1)&![X3]:(((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))=>~((v4_tex_2(X3,X1)&X2=u1_struct_0(X3)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_tex_2)).
% 0.12/0.38  fof(d7_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>(v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X3,X1)&r1_tarski(X2,X3))=>X2=X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 0.12/0.38  fof(t34_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~((v2_tex_2(X2,X1)&![X3]:((((~(v2_struct_0(X3))&v1_pre_topc(X3))&v1_tdlat_3(X3))&m1_pre_topc(X3,X1))=>X2!=u1_struct_0(X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tex_2)).
% 0.12/0.38  fof(d8_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>(v4_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v3_tex_2(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tex_2)).
% 0.12/0.38  fof(c_0_4, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~((v3_tex_2(X2,X1)&![X3]:(((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))=>~((v4_tex_2(X3,X1)&X2=u1_struct_0(X3))))))))), inference(assume_negation,[status(cth)],[t53_tex_2])).
% 0.12/0.38  fof(c_0_5, plain, ![X4, X5, X6]:(((v2_tex_2(X5,X4)|~v3_tex_2(X5,X4)|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X4))&(~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))|(~v2_tex_2(X6,X4)|~r1_tarski(X5,X6)|X5=X6)|~v3_tex_2(X5,X4)|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X4)))&((m1_subset_1(esk1_2(X4,X5),k1_zfmisc_1(u1_struct_0(X4)))|~v2_tex_2(X5,X4)|v3_tex_2(X5,X4)|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X4))&(((v2_tex_2(esk1_2(X4,X5),X4)|~v2_tex_2(X5,X4)|v3_tex_2(X5,X4)|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X4))&(r1_tarski(X5,esk1_2(X4,X5))|~v2_tex_2(X5,X4)|v3_tex_2(X5,X4)|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X4)))&(X5!=esk1_2(X4,X5)|~v2_tex_2(X5,X4)|v3_tex_2(X5,X4)|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X4))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).
% 0.12/0.38  fof(c_0_6, negated_conjecture, ![X17]:(((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&((~v1_xboole_0(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))))&(v3_tex_2(esk5_0,esk4_0)&(v2_struct_0(X17)|~v1_pre_topc(X17)|~m1_pre_topc(X17,esk4_0)|(~v4_tex_2(X17,esk4_0)|esk5_0!=u1_struct_0(X17)))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).
% 0.12/0.38  fof(c_0_7, plain, ![X12, X13]:(((((~v2_struct_0(esk3_2(X12,X13))|~v2_tex_2(X13,X12)|(v1_xboole_0(X13)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(v1_pre_topc(esk3_2(X12,X13))|~v2_tex_2(X13,X12)|(v1_xboole_0(X13)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12))))&(v1_tdlat_3(esk3_2(X12,X13))|~v2_tex_2(X13,X12)|(v1_xboole_0(X13)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12))))&(m1_pre_topc(esk3_2(X12,X13),X12)|~v2_tex_2(X13,X12)|(v1_xboole_0(X13)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12))))&(X13=u1_struct_0(esk3_2(X12,X13))|~v2_tex_2(X13,X12)|(v1_xboole_0(X13)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).
% 0.12/0.38  cnf(c_0_8, plain, (v2_tex_2(X1,X2)|~v3_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.38  cnf(c_0_9, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.38  cnf(c_0_10, negated_conjecture, (v3_tex_2(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.38  cnf(c_0_11, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.38  cnf(c_0_12, plain, (v1_pre_topc(esk3_2(X1,X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.38  cnf(c_0_13, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.38  cnf(c_0_14, negated_conjecture, (v2_tex_2(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10]), c_0_11])])).
% 0.12/0.38  cnf(c_0_15, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.38  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.38  cnf(c_0_17, plain, (v1_xboole_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk3_2(X1,X2))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.38  cnf(c_0_18, negated_conjecture, (v2_struct_0(X1)|~v1_pre_topc(X1)|~m1_pre_topc(X1,esk4_0)|~v4_tex_2(X1,esk4_0)|esk5_0!=u1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.38  cnf(c_0_19, negated_conjecture, (v1_pre_topc(esk3_2(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_9]), c_0_13]), c_0_14]), c_0_11])]), c_0_15]), c_0_16])).
% 0.12/0.38  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk3_2(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_9]), c_0_13]), c_0_14]), c_0_11])]), c_0_15]), c_0_16])).
% 0.12/0.38  cnf(c_0_21, plain, (X1=u1_struct_0(esk3_2(X2,X1))|v1_xboole_0(X1)|v2_struct_0(X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.38  cnf(c_0_22, negated_conjecture, (u1_struct_0(esk3_2(esk4_0,esk5_0))!=esk5_0|~v4_tex_2(esk3_2(esk4_0,esk5_0),esk4_0)|~m1_pre_topc(esk3_2(esk4_0,esk5_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.12/0.38  cnf(c_0_23, negated_conjecture, (u1_struct_0(esk3_2(esk4_0,esk5_0))=esk5_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_9]), c_0_13]), c_0_14]), c_0_11])]), c_0_15]), c_0_16])).
% 0.12/0.38  cnf(c_0_24, plain, (m1_pre_topc(esk3_2(X1,X2),X1)|v1_xboole_0(X2)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.38  fof(c_0_25, plain, ![X8, X9, X10]:((~v4_tex_2(X9,X8)|(~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|(X10!=u1_struct_0(X9)|v3_tex_2(X10,X8)))|~m1_pre_topc(X9,X8)|(v2_struct_0(X8)|~l1_pre_topc(X8)))&((m1_subset_1(esk2_2(X8,X9),k1_zfmisc_1(u1_struct_0(X8)))|v4_tex_2(X9,X8)|~m1_pre_topc(X9,X8)|(v2_struct_0(X8)|~l1_pre_topc(X8)))&((esk2_2(X8,X9)=u1_struct_0(X9)|v4_tex_2(X9,X8)|~m1_pre_topc(X9,X8)|(v2_struct_0(X8)|~l1_pre_topc(X8)))&(~v3_tex_2(esk2_2(X8,X9),X8)|v4_tex_2(X9,X8)|~m1_pre_topc(X9,X8)|(v2_struct_0(X8)|~l1_pre_topc(X8)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_tex_2])])])])])])).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, (~v4_tex_2(esk3_2(esk4_0,esk5_0),esk4_0)|~m1_pre_topc(esk3_2(esk4_0,esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23])])).
% 0.12/0.38  cnf(c_0_27, negated_conjecture, (m1_pre_topc(esk3_2(esk4_0,esk5_0),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_9]), c_0_13]), c_0_14]), c_0_11])]), c_0_15]), c_0_16])).
% 0.12/0.38  cnf(c_0_28, plain, (esk2_2(X1,X2)=u1_struct_0(X2)|v4_tex_2(X2,X1)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.38  cnf(c_0_29, negated_conjecture, (~v4_tex_2(esk3_2(esk4_0,esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27])])).
% 0.12/0.38  cnf(c_0_30, plain, (v4_tex_2(X2,X1)|v2_struct_0(X1)|~v3_tex_2(esk2_2(X1,X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.38  cnf(c_0_31, negated_conjecture, (esk2_2(esk4_0,esk3_2(esk4_0,esk5_0))=esk5_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_27]), c_0_23]), c_0_11])]), c_0_16]), c_0_29])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_27]), c_0_10]), c_0_11])]), c_0_29]), c_0_16]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 33
% 0.12/0.38  # Proof object clause steps            : 24
% 0.12/0.38  # Proof object formula steps           : 9
% 0.12/0.38  # Proof object conjectures             : 20
% 0.12/0.38  # Proof object clause conjectures      : 17
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 14
% 0.12/0.38  # Proof object initial formulas used   : 4
% 0.12/0.38  # Proof object generating inferences   : 8
% 0.12/0.38  # Proof object simplifying inferences  : 43
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 4
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 22
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 22
% 0.12/0.38  # Processed clauses                    : 64
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 0
% 0.12/0.38  # ...remaining for further processing  : 64
% 0.12/0.38  # Other redundant clauses eliminated   : 1
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 0
% 0.12/0.38  # Backward-rewritten                   : 2
% 0.12/0.38  # Generated clauses                    : 27
% 0.12/0.38  # ...of the previous two non-trivial   : 25
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 26
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 1
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 39
% 0.12/0.38  #    Positive orientable unit clauses  : 10
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 4
% 0.12/0.38  #    Non-unit-clauses                  : 25
% 0.12/0.38  # Current number of unprocessed clauses: 5
% 0.12/0.38  # ...number of literals in the above   : 25
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 24
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 298
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 4
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.38  # Unit Clause-clause subsumption calls : 19
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 2
% 0.12/0.38  # BW rewrite match successes           : 2
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 3456
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.032 s
% 0.12/0.38  # System time              : 0.004 s
% 0.12/0.38  # Total time               : 0.036 s
% 0.12/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
