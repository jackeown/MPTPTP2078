%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:44 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 269 expanded)
%              Number of clauses        :   24 (  84 expanded)
%              Number of leaves         :    4 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :  213 (2441 expanded)
%              Number of equality atoms :   16 ( 199 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_tex_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

fof(t51_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( v3_tex_2(X3,X1)
                <=> v4_tex_2(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_tex_2)).

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
    ! [X16] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v1_xboole_0(esk4_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & v3_tex_2(esk4_0,esk3_0)
      & ( v2_struct_0(X16)
        | ~ v1_pre_topc(X16)
        | ~ m1_pre_topc(X16,esk3_0)
        | ~ v4_tex_2(X16,esk3_0)
        | esk4_0 != u1_struct_0(X16) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).

fof(c_0_7,plain,(
    ! [X8,X9] :
      ( ( ~ v2_struct_0(esk2_2(X8,X9))
        | ~ v2_tex_2(X9,X8)
        | v1_xboole_0(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( v1_pre_topc(esk2_2(X8,X9))
        | ~ v2_tex_2(X9,X8)
        | v1_xboole_0(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( v1_tdlat_3(esk2_2(X8,X9))
        | ~ v2_tex_2(X9,X8)
        | v1_xboole_0(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( m1_pre_topc(esk2_2(X8,X9),X8)
        | ~ v2_tex_2(X9,X8)
        | v1_xboole_0(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( X9 = u1_struct_0(esk2_2(X8,X9))
        | ~ v2_tex_2(X9,X8)
        | v1_xboole_0(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).

cnf(c_0_8,plain,
    ( v2_tex_2(X1,X2)
    | ~ v3_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v3_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk2_2(X1,X2))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_16,plain,(
    ! [X11,X12,X13] :
      ( ( ~ v3_tex_2(X13,X11)
        | v4_tex_2(X12,X11)
        | X13 != u1_struct_0(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ m1_pre_topc(X12,X11)
        | v2_struct_0(X11)
        | ~ l1_pre_topc(X11) )
      & ( ~ v4_tex_2(X12,X11)
        | v3_tex_2(X13,X11)
        | X13 != u1_struct_0(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ m1_pre_topc(X12,X11)
        | v2_struct_0(X11)
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t51_tex_2])])])])])).

cnf(c_0_17,plain,
    ( v1_pre_topc(esk2_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( v2_tex_2(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk2_2(esk3_0,esk4_0))
    | ~ v2_tex_2(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_10]),c_0_13]),c_0_11])]),c_0_14]),c_0_15])).

cnf(c_0_20,plain,
    ( v4_tex_2(X3,X2)
    | v2_struct_0(X2)
    | ~ v3_tex_2(X1,X2)
    | X1 != u1_struct_0(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( X1 = u1_struct_0(esk2_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ v4_tex_2(X1,esk3_0)
    | esk4_0 != u1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( v1_pre_topc(esk2_2(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_10]),c_0_13]),c_0_18]),c_0_11])]),c_0_14]),c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk2_2(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_18])])).

cnf(c_0_25,plain,
    ( m1_pre_topc(esk2_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,plain,
    ( v4_tex_2(X1,X2)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v3_tex_2(u1_struct_0(X1),X2)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( u1_struct_0(esk2_2(esk3_0,esk4_0)) = esk4_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_10]),c_0_13]),c_0_18]),c_0_11])]),c_0_14]),c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( u1_struct_0(esk2_2(esk3_0,esk4_0)) != esk4_0
    | ~ v4_tex_2(esk2_2(esk3_0,esk4_0),esk3_0)
    | ~ m1_pre_topc(esk2_2(esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( m1_pre_topc(esk2_2(esk3_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_10]),c_0_13]),c_0_18]),c_0_11])]),c_0_14]),c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( v4_tex_2(esk2_2(esk3_0,esk4_0),X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk2_2(esk3_0,esk4_0),X1)
    | ~ v3_tex_2(esk4_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( ~ v4_tex_2(esk2_2(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_27])]),c_0_29])])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_29]),c_0_9]),c_0_10]),c_0_11])]),c_0_31]),c_0_15]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:21:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t53_tex_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~((v3_tex_2(X2,X1)&![X3]:(((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))=>~((v4_tex_2(X3,X1)&X2=u1_struct_0(X3)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_tex_2)).
% 0.12/0.37  fof(d7_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>(v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X3,X1)&r1_tarski(X2,X3))=>X2=X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 0.12/0.37  fof(t34_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~((v2_tex_2(X2,X1)&![X3]:((((~(v2_struct_0(X3))&v1_pre_topc(X3))&v1_tdlat_3(X3))&m1_pre_topc(X3,X1))=>X2!=u1_struct_0(X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 0.12/0.37  fof(t51_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>(v3_tex_2(X3,X1)<=>v4_tex_2(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_tex_2)).
% 0.12/0.37  fof(c_0_4, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~((v3_tex_2(X2,X1)&![X3]:(((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))=>~((v4_tex_2(X3,X1)&X2=u1_struct_0(X3))))))))), inference(assume_negation,[status(cth)],[t53_tex_2])).
% 0.12/0.37  fof(c_0_5, plain, ![X4, X5, X6]:(((v2_tex_2(X5,X4)|~v3_tex_2(X5,X4)|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X4))&(~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))|(~v2_tex_2(X6,X4)|~r1_tarski(X5,X6)|X5=X6)|~v3_tex_2(X5,X4)|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X4)))&((m1_subset_1(esk1_2(X4,X5),k1_zfmisc_1(u1_struct_0(X4)))|~v2_tex_2(X5,X4)|v3_tex_2(X5,X4)|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X4))&(((v2_tex_2(esk1_2(X4,X5),X4)|~v2_tex_2(X5,X4)|v3_tex_2(X5,X4)|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X4))&(r1_tarski(X5,esk1_2(X4,X5))|~v2_tex_2(X5,X4)|v3_tex_2(X5,X4)|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X4)))&(X5!=esk1_2(X4,X5)|~v2_tex_2(X5,X4)|v3_tex_2(X5,X4)|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X4))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).
% 0.12/0.37  fof(c_0_6, negated_conjecture, ![X16]:(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v1_xboole_0(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))))&(v3_tex_2(esk4_0,esk3_0)&(v2_struct_0(X16)|~v1_pre_topc(X16)|~m1_pre_topc(X16,esk3_0)|(~v4_tex_2(X16,esk3_0)|esk4_0!=u1_struct_0(X16)))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])).
% 0.12/0.37  fof(c_0_7, plain, ![X8, X9]:(((((~v2_struct_0(esk2_2(X8,X9))|~v2_tex_2(X9,X8)|(v1_xboole_0(X9)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8))))|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)))&(v1_pre_topc(esk2_2(X8,X9))|~v2_tex_2(X9,X8)|(v1_xboole_0(X9)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8))))|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8))))&(v1_tdlat_3(esk2_2(X8,X9))|~v2_tex_2(X9,X8)|(v1_xboole_0(X9)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8))))|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8))))&(m1_pre_topc(esk2_2(X8,X9),X8)|~v2_tex_2(X9,X8)|(v1_xboole_0(X9)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8))))|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8))))&(X9=u1_struct_0(esk2_2(X8,X9))|~v2_tex_2(X9,X8)|(v1_xboole_0(X9)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8))))|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).
% 0.12/0.37  cnf(c_0_8, plain, (v2_tex_2(X1,X2)|~v3_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_9, negated_conjecture, (v3_tex_2(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_11, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_12, plain, (v1_xboole_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk2_2(X1,X2))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_13, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_14, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  fof(c_0_16, plain, ![X11, X12, X13]:((~v3_tex_2(X13,X11)|v4_tex_2(X12,X11)|X13!=u1_struct_0(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))|~m1_pre_topc(X12,X11)|(v2_struct_0(X11)|~l1_pre_topc(X11)))&(~v4_tex_2(X12,X11)|v3_tex_2(X13,X11)|X13!=u1_struct_0(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))|~m1_pre_topc(X12,X11)|(v2_struct_0(X11)|~l1_pre_topc(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t51_tex_2])])])])])).
% 0.12/0.37  cnf(c_0_17, plain, (v1_pre_topc(esk2_2(X1,X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (v2_tex_2(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10]), c_0_11])])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk2_2(esk3_0,esk4_0))|~v2_tex_2(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_10]), c_0_13]), c_0_11])]), c_0_14]), c_0_15])).
% 0.12/0.37  cnf(c_0_20, plain, (v4_tex_2(X3,X2)|v2_struct_0(X2)|~v3_tex_2(X1,X2)|X1!=u1_struct_0(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_21, plain, (X1=u1_struct_0(esk2_2(X2,X1))|v1_xboole_0(X1)|v2_struct_0(X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (v2_struct_0(X1)|~v1_pre_topc(X1)|~m1_pre_topc(X1,esk3_0)|~v4_tex_2(X1,esk3_0)|esk4_0!=u1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (v1_pre_topc(esk2_2(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_10]), c_0_13]), c_0_18]), c_0_11])]), c_0_14]), c_0_15])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk2_2(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_18])])).
% 0.12/0.37  cnf(c_0_25, plain, (m1_pre_topc(esk2_2(X1,X2),X1)|v1_xboole_0(X2)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_26, plain, (v4_tex_2(X1,X2)|v2_struct_0(X2)|~m1_pre_topc(X1,X2)|~v3_tex_2(u1_struct_0(X1),X2)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(er,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (u1_struct_0(esk2_2(esk3_0,esk4_0))=esk4_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_10]), c_0_13]), c_0_18]), c_0_11])]), c_0_14]), c_0_15])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (u1_struct_0(esk2_2(esk3_0,esk4_0))!=esk4_0|~v4_tex_2(esk2_2(esk3_0,esk4_0),esk3_0)|~m1_pre_topc(esk2_2(esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (m1_pre_topc(esk2_2(esk3_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_10]), c_0_13]), c_0_18]), c_0_11])]), c_0_14]), c_0_15])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (v4_tex_2(esk2_2(esk3_0,esk4_0),X1)|v2_struct_0(X1)|~m1_pre_topc(esk2_2(esk3_0,esk4_0),X1)|~v3_tex_2(esk4_0,X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (~v4_tex_2(esk2_2(esk3_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_27])]), c_0_29])])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_29]), c_0_9]), c_0_10]), c_0_11])]), c_0_31]), c_0_15]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 33
% 0.12/0.37  # Proof object clause steps            : 24
% 0.12/0.37  # Proof object formula steps           : 9
% 0.12/0.37  # Proof object conjectures             : 20
% 0.12/0.37  # Proof object clause conjectures      : 17
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 13
% 0.12/0.37  # Proof object initial formulas used   : 4
% 0.12/0.37  # Proof object generating inferences   : 8
% 0.12/0.37  # Proof object simplifying inferences  : 40
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 4
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 20
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 20
% 0.12/0.37  # Processed clauses                    : 55
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 55
% 0.12/0.37  # Other redundant clauses eliminated   : 2
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 2
% 0.12/0.37  # Generated clauses                    : 27
% 0.12/0.37  # ...of the previous two non-trivial   : 25
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 25
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 2
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 31
% 0.12/0.37  #    Positive orientable unit clauses  : 9
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 4
% 0.12/0.37  #    Non-unit-clauses                  : 18
% 0.12/0.37  # Current number of unprocessed clauses: 10
% 0.12/0.37  # ...number of literals in the above   : 56
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 22
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 196
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 4
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 3
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 2
% 0.12/0.37  # BW rewrite match successes           : 2
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 3141
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.031 s
% 0.12/0.37  # System time              : 0.003 s
% 0.12/0.37  # Total time               : 0.034 s
% 0.12/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
