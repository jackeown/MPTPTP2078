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
% DateTime   : Thu Dec  3 11:20:02 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   28 (  72 expanded)
%              Number of clauses        :   19 (  23 expanded)
%              Number of leaves         :    4 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :  207 ( 963 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   46 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t30_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v3_pre_topc(X2,X1)
                    & v3_pre_topc(X3,X1) )
                 => ( v3_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1)
                    & v3_pre_topc(k4_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v3_pre_topc(X2,X1)
                    & v3_pre_topc(X3,X1)
                    & v2_tex_2(X2,X1)
                    & v2_tex_2(X3,X1) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tex_2)).

fof(t37_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X2,X1)
                  & v3_pre_topc(X3,X1) )
               => v3_pre_topc(k4_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_tops_1)).

fof(t38_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X2,X1)
                  & v3_pre_topc(X3,X1)
                  & v2_tex_2(X2,X1)
                  & v2_tex_2(X3,X1) )
               => v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tex_2)).

fof(t38_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X2,X1)
                  & v3_pre_topc(X3,X1) )
               => v3_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_1)).

fof(c_0_4,plain,(
    ! [X10,X13,X14] :
      ( ( m1_subset_1(esk1_1(X10),k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ v3_pre_topc(X13,X10)
        | ~ v3_pre_topc(X14,X10)
        | ~ v2_tex_2(X13,X10)
        | ~ v2_tex_2(X14,X10)
        | v2_tex_2(k4_subset_1(u1_struct_0(X10),X13,X14),X10)
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk2_1(X10),k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ v3_pre_topc(X13,X10)
        | ~ v3_pre_topc(X14,X10)
        | ~ v2_tex_2(X13,X10)
        | ~ v2_tex_2(X14,X10)
        | v2_tex_2(k4_subset_1(u1_struct_0(X10),X13,X14),X10)
        | ~ l1_pre_topc(X10) )
      & ( v3_pre_topc(esk1_1(X10),X10)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ v3_pre_topc(X13,X10)
        | ~ v3_pre_topc(X14,X10)
        | ~ v2_tex_2(X13,X10)
        | ~ v2_tex_2(X14,X10)
        | v2_tex_2(k4_subset_1(u1_struct_0(X10),X13,X14),X10)
        | ~ l1_pre_topc(X10) )
      & ( v3_pre_topc(esk2_1(X10),X10)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ v3_pre_topc(X13,X10)
        | ~ v3_pre_topc(X14,X10)
        | ~ v2_tex_2(X13,X10)
        | ~ v2_tex_2(X14,X10)
        | v2_tex_2(k4_subset_1(u1_struct_0(X10),X13,X14),X10)
        | ~ l1_pre_topc(X10) )
      & ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(X10),esk1_1(X10),esk2_1(X10)),X10)
        | ~ v3_pre_topc(k4_subset_1(u1_struct_0(X10),esk1_1(X10),esk2_1(X10)),X10)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ v3_pre_topc(X13,X10)
        | ~ v3_pre_topc(X14,X10)
        | ~ v2_tex_2(X13,X10)
        | ~ v2_tex_2(X14,X10)
        | v2_tex_2(k4_subset_1(u1_struct_0(X10),X13,X14),X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tex_2])])])])])).

fof(c_0_5,plain,(
    ! [X4,X5,X6] :
      ( ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ v3_pre_topc(X5,X4)
      | ~ v3_pre_topc(X6,X4)
      | v3_pre_topc(k4_subset_1(u1_struct_0(X4),X5,X6),X4) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_tops_1])])])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v3_pre_topc(X2,X1)
                    & v3_pre_topc(X3,X1)
                    & v2_tex_2(X2,X1)
                    & v2_tex_2(X3,X1) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t38_tex_2])).

cnf(c_0_7,plain,
    ( v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v3_pre_topc(k9_subset_1(u1_struct_0(X1),esk1_1(X1),esk2_1(X1)),X1)
    | ~ v3_pre_topc(k4_subset_1(u1_struct_0(X1),esk1_1(X1),esk2_1(X1)),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v3_pre_topc(X3,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tex_2(X3,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( v3_pre_topc(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v3_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v3_pre_topc(X3,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tex_2(X3,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v3_pre_topc(X3,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tex_2(X3,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,plain,
    ( v3_pre_topc(esk1_1(X1),X1)
    | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v3_pre_topc(X3,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tex_2(X3,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,plain,
    ( v3_pre_topc(esk2_1(X1),X1)
    | v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v3_pre_topc(X3,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tex_2(X3,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_13,plain,(
    ! [X7,X8,X9] :
      ( ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X7)))
      | ~ v3_pre_topc(X8,X7)
      | ~ v3_pre_topc(X9,X7)
      | v3_pre_topc(k9_subset_1(u1_struct_0(X7),X8,X9),X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_tops_1])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & v3_pre_topc(esk4_0,esk3_0)
    & v3_pre_topc(esk5_0,esk3_0)
    & v2_tex_2(esk4_0,esk3_0)
    & v2_tex_2(esk5_0,esk3_0)
    & ~ v2_tex_2(k4_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

cnf(c_0_15,plain,
    ( v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v2_tex_2(X3,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ v3_pre_topc(k9_subset_1(u1_struct_0(X1),esk1_1(X1),esk2_1(X1)),X1)
    | ~ v3_pre_topc(X3,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_16,plain,
    ( v3_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v3_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_tex_2(k4_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)
    | ~ v2_tex_2(X3,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ v3_pre_topc(X3,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v2_tex_2(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v2_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v3_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:52:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t30_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>(![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&v3_pre_topc(X3,X1))=>(v3_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1)&v3_pre_topc(k4_subset_1(u1_struct_0(X1),X2,X3),X1)))))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((((v3_pre_topc(X2,X1)&v3_pre_topc(X3,X1))&v2_tex_2(X2,X1))&v2_tex_2(X3,X1))=>v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tex_2)).
% 0.14/0.38  fof(t37_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&v3_pre_topc(X3,X1))=>v3_pre_topc(k4_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_tops_1)).
% 0.14/0.38  fof(t38_tex_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((((v3_pre_topc(X2,X1)&v3_pre_topc(X3,X1))&v2_tex_2(X2,X1))&v2_tex_2(X3,X1))=>v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_tex_2)).
% 0.14/0.38  fof(t38_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&v3_pre_topc(X3,X1))=>v3_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_tops_1)).
% 0.14/0.38  fof(c_0_4, plain, ![X10, X13, X14]:((m1_subset_1(esk1_1(X10),k1_zfmisc_1(u1_struct_0(X10)))|(~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X10)))|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X10)))|(~v3_pre_topc(X13,X10)|~v3_pre_topc(X14,X10)|~v2_tex_2(X13,X10)|~v2_tex_2(X14,X10)|v2_tex_2(k4_subset_1(u1_struct_0(X10),X13,X14),X10))))|~l1_pre_topc(X10))&((m1_subset_1(esk2_1(X10),k1_zfmisc_1(u1_struct_0(X10)))|(~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X10)))|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X10)))|(~v3_pre_topc(X13,X10)|~v3_pre_topc(X14,X10)|~v2_tex_2(X13,X10)|~v2_tex_2(X14,X10)|v2_tex_2(k4_subset_1(u1_struct_0(X10),X13,X14),X10))))|~l1_pre_topc(X10))&(((v3_pre_topc(esk1_1(X10),X10)|(~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X10)))|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X10)))|(~v3_pre_topc(X13,X10)|~v3_pre_topc(X14,X10)|~v2_tex_2(X13,X10)|~v2_tex_2(X14,X10)|v2_tex_2(k4_subset_1(u1_struct_0(X10),X13,X14),X10))))|~l1_pre_topc(X10))&(v3_pre_topc(esk2_1(X10),X10)|(~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X10)))|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X10)))|(~v3_pre_topc(X13,X10)|~v3_pre_topc(X14,X10)|~v2_tex_2(X13,X10)|~v2_tex_2(X14,X10)|v2_tex_2(k4_subset_1(u1_struct_0(X10),X13,X14),X10))))|~l1_pre_topc(X10)))&(~v3_pre_topc(k9_subset_1(u1_struct_0(X10),esk1_1(X10),esk2_1(X10)),X10)|~v3_pre_topc(k4_subset_1(u1_struct_0(X10),esk1_1(X10),esk2_1(X10)),X10)|(~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X10)))|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X10)))|(~v3_pre_topc(X13,X10)|~v3_pre_topc(X14,X10)|~v2_tex_2(X13,X10)|~v2_tex_2(X14,X10)|v2_tex_2(k4_subset_1(u1_struct_0(X10),X13,X14),X10))))|~l1_pre_topc(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tex_2])])])])])).
% 0.14/0.38  fof(c_0_5, plain, ![X4, X5, X6]:(~v2_pre_topc(X4)|~l1_pre_topc(X4)|(~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|(~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))|(~v3_pre_topc(X5,X4)|~v3_pre_topc(X6,X4)|v3_pre_topc(k4_subset_1(u1_struct_0(X4),X5,X6),X4))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_tops_1])])])).
% 0.14/0.38  fof(c_0_6, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((((v3_pre_topc(X2,X1)&v3_pre_topc(X3,X1))&v2_tex_2(X2,X1))&v2_tex_2(X3,X1))=>v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)))))), inference(assume_negation,[status(cth)],[t38_tex_2])).
% 0.14/0.38  cnf(c_0_7, plain, (v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)|~v3_pre_topc(k9_subset_1(u1_struct_0(X1),esk1_1(X1),esk2_1(X1)),X1)|~v3_pre_topc(k4_subset_1(u1_struct_0(X1),esk1_1(X1),esk2_1(X1)),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~v3_pre_topc(X3,X1)|~v2_tex_2(X2,X1)|~v2_tex_2(X3,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.14/0.38  cnf(c_0_8, plain, (v3_pre_topc(k4_subset_1(u1_struct_0(X1),X2,X3),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~v3_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.38  cnf(c_0_9, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~v3_pre_topc(X3,X1)|~v2_tex_2(X2,X1)|~v2_tex_2(X3,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.14/0.38  cnf(c_0_10, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~v3_pre_topc(X3,X1)|~v2_tex_2(X2,X1)|~v2_tex_2(X3,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.14/0.38  cnf(c_0_11, plain, (v3_pre_topc(esk1_1(X1),X1)|v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~v3_pre_topc(X3,X1)|~v2_tex_2(X2,X1)|~v2_tex_2(X3,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.14/0.38  cnf(c_0_12, plain, (v3_pre_topc(esk2_1(X1),X1)|v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~v3_pre_topc(X3,X1)|~v2_tex_2(X2,X1)|~v2_tex_2(X3,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.14/0.38  fof(c_0_13, plain, ![X7, X8, X9]:(~v2_pre_topc(X7)|~l1_pre_topc(X7)|(~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|(~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X7)))|(~v3_pre_topc(X8,X7)|~v3_pre_topc(X9,X7)|v3_pre_topc(k9_subset_1(u1_struct_0(X7),X8,X9),X7))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_tops_1])])])).
% 0.14/0.38  fof(c_0_14, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((((v3_pre_topc(esk4_0,esk3_0)&v3_pre_topc(esk5_0,esk3_0))&v2_tex_2(esk4_0,esk3_0))&v2_tex_2(esk5_0,esk3_0))&~v2_tex_2(k4_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_0),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).
% 0.14/0.38  cnf(c_0_15, plain, (v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)|~v2_tex_2(X3,X1)|~v2_tex_2(X2,X1)|~v3_pre_topc(k9_subset_1(u1_struct_0(X1),esk1_1(X1),esk2_1(X1)),X1)|~v3_pre_topc(X3,X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12])).
% 0.14/0.38  cnf(c_0_16, plain, (v3_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X3),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~v3_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (~v2_tex_2(k4_subset_1(u1_struct_0(esk3_0),esk4_0,esk5_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_18, plain, (v2_tex_2(k4_subset_1(u1_struct_0(X1),X2,X3),X1)|~v2_tex_2(X3,X1)|~v2_tex_2(X2,X1)|~v3_pre_topc(X3,X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_9]), c_0_10]), c_0_11]), c_0_12])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (v2_tex_2(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_20, negated_conjecture, (v2_tex_2(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (v3_pre_topc(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (v3_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 28
% 0.14/0.38  # Proof object clause steps            : 19
% 0.14/0.38  # Proof object formula steps           : 9
% 0.14/0.38  # Proof object conjectures             : 13
% 0.14/0.38  # Proof object clause conjectures      : 10
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 16
% 0.14/0.38  # Proof object initial formulas used   : 4
% 0.14/0.38  # Proof object generating inferences   : 3
% 0.14/0.38  # Proof object simplifying inferences  : 17
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 4
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 17
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 17
% 0.14/0.38  # Processed clauses                    : 49
% 0.14/0.38  # ...of these trivial                  : 3
% 0.21/0.38  # ...subsumed                          : 0
% 0.21/0.38  # ...remaining for further processing  : 46
% 0.21/0.38  # Other redundant clauses eliminated   : 0
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 1
% 0.21/0.38  # Backward-rewritten                   : 6
% 0.21/0.38  # Generated clauses                    : 30
% 0.21/0.38  # ...of the previous two non-trivial   : 22
% 0.21/0.38  # Contextual simplify-reflections      : 8
% 0.21/0.38  # Paramodulations                      : 30
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 0
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 22
% 0.21/0.38  #    Positive orientable unit clauses  : 12
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 2
% 0.21/0.38  #    Non-unit-clauses                  : 8
% 0.21/0.38  # Current number of unprocessed clauses: 0
% 0.21/0.38  # ...number of literals in the above   : 0
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 24
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 143
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 10
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 9
% 0.21/0.38  # Unit Clause-clause subsumption calls : 0
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 4
% 0.21/0.38  # BW rewrite match successes           : 4
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 3391
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.032 s
% 0.21/0.38  # System time              : 0.002 s
% 0.21/0.38  # Total time               : 0.034 s
% 0.21/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
