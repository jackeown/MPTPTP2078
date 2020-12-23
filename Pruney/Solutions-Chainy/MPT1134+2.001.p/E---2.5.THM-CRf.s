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
% DateTime   : Thu Dec  3 11:09:27 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 174 expanded)
%              Number of clauses        :   26 (  73 expanded)
%              Number of leaves         :    6 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :  142 ( 632 expanded)
%              Number of equality atoms :   25 (  58 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( l1_pre_topc(X3)
             => ! [X4] :
                  ( l1_pre_topc(X4)
                 => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                      & g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))
                      & m1_pre_topc(X3,X1) )
                   => m1_pre_topc(X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t65_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(c_0_6,plain,(
    ! [X11,X12,X13,X14] :
      ( ~ l1_pre_topc(X11)
      | ~ l1_pre_topc(X12)
      | ~ l1_pre_topc(X13)
      | ~ l1_pre_topc(X14)
      | g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11)) != g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12))
      | g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)) != g1_pre_topc(u1_struct_0(X14),u1_pre_topc(X14))
      | ~ m1_pre_topc(X13,X11)
      | m1_pre_topc(X14,X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_pre_topc])])])).

fof(c_0_7,plain,(
    ! [X8,X9] :
      ( ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(X9,X8)
      | l1_pre_topc(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ( m1_pre_topc(X1,X2)
            <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t65_pre_topc])).

cnf(c_0_9,plain,
    ( m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X4)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & l1_pre_topc(esk2_0)
    & ( ~ m1_pre_topc(esk1_0,esk2_0)
      | ~ m1_pre_topc(esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) )
    & ( m1_pre_topc(esk1_0,esk2_0)
      | m1_pre_topc(esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_12,plain,(
    ! [X6,X7] :
      ( ( v1_pre_topc(g1_pre_topc(X6,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X6))) )
      & ( l1_pre_topc(g1_pre_topc(X6,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X6))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

fof(c_0_13,plain,(
    ! [X10] :
      ( ~ l1_pre_topc(X10)
      | m1_subset_1(u1_pre_topc(X10),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_14,plain,
    ( m1_pre_topc(X1,X2)
    | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4) ),
    inference(csr,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk2_0)
    | m1_pre_topc(esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk2_0)
    | m1_pre_topc(X1,X2)
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_21,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | ~ v1_pre_topc(X5)
      | X5 = g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_22,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk2_0)
    | m1_pre_topc(X1,X2)
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_23,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,plain,
    ( v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk2_0)
    | m1_pre_topc(X1,X2)
    | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk2_0)
    | m1_pre_topc(X1,X2)
    | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_20])])).

cnf(c_0_28,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk2_0)
    | m1_pre_topc(X1,X2)
    | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_19]),c_0_20])])).

cnf(c_0_29,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk2_0)
    | m1_pre_topc(X1,esk2_0)
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_20])])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_29]),c_0_30])])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(X1,X2)
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_31]),c_0_20])])).

cnf(c_0_33,negated_conjecture,
    ( ~ m1_pre_topc(esk1_0,esk2_0)
    | ~ m1_pre_topc(esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_34,negated_conjecture,
    ( m1_pre_topc(esk1_0,X1)
    | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_30])])).

cnf(c_0_35,negated_conjecture,
    ( ~ m1_pre_topc(esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_31])])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_23])]),c_0_35])).

cnf(c_0_37,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_26]),c_0_20])])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_19]),c_0_20])]),
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
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.027 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t31_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(l1_pre_topc(X3)=>![X4]:(l1_pre_topc(X4)=>(((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))&m1_pre_topc(X3,X1))=>m1_pre_topc(X4,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_pre_topc)).
% 0.19/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.38  fof(t65_pre_topc, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.19/0.38  fof(dt_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v1_pre_topc(g1_pre_topc(X1,X2))&l1_pre_topc(g1_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 0.19/0.38  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.19/0.38  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.19/0.38  fof(c_0_6, plain, ![X11, X12, X13, X14]:(~l1_pre_topc(X11)|(~l1_pre_topc(X12)|(~l1_pre_topc(X13)|(~l1_pre_topc(X14)|(g1_pre_topc(u1_struct_0(X11),u1_pre_topc(X11))!=g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12))|g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))!=g1_pre_topc(u1_struct_0(X14),u1_pre_topc(X14))|~m1_pre_topc(X13,X11)|m1_pre_topc(X14,X12)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_pre_topc])])])).
% 0.19/0.38  fof(c_0_7, plain, ![X8, X9]:(~l1_pre_topc(X8)|(~m1_pre_topc(X9,X8)|l1_pre_topc(X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))), inference(assume_negation,[status(cth)],[t65_pre_topc])).
% 0.19/0.38  cnf(c_0_9, plain, (m1_pre_topc(X4,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X4)|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))!=g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_10, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  fof(c_0_11, negated_conjecture, (l1_pre_topc(esk1_0)&(l1_pre_topc(esk2_0)&((~m1_pre_topc(esk1_0,esk2_0)|~m1_pre_topc(esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))&(m1_pre_topc(esk1_0,esk2_0)|m1_pre_topc(esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.19/0.38  fof(c_0_12, plain, ![X6, X7]:((v1_pre_topc(g1_pre_topc(X6,X7))|~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X6))))&(l1_pre_topc(g1_pre_topc(X6,X7))|~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X6))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).
% 0.19/0.38  fof(c_0_13, plain, ![X10]:(~l1_pre_topc(X10)|m1_subset_1(u1_pre_topc(X10),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.19/0.38  cnf(c_0_14, plain, (m1_pre_topc(X1,X2)|g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))!=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|~m1_pre_topc(X3,X4)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X4)), inference(csr,[status(thm)],[c_0_9, c_0_10])).
% 0.19/0.38  cnf(c_0_15, negated_conjecture, (m1_pre_topc(esk1_0,esk2_0)|m1_pre_topc(esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_16, plain, (l1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_17, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (m1_pre_topc(esk1_0,esk2_0)|m1_pre_topc(X1,X2)|g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))!=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.38  cnf(c_0_19, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  fof(c_0_21, plain, ![X5]:(~l1_pre_topc(X5)|(~v1_pre_topc(X5)|X5=g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (m1_pre_topc(esk1_0,esk2_0)|m1_pre_topc(X1,X2)|g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),u1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))!=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.19/0.38  cnf(c_0_23, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_24, plain, (v1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (m1_pre_topc(esk1_0,esk2_0)|m1_pre_topc(X1,X2)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~v1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.38  cnf(c_0_26, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_24, c_0_17])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (m1_pre_topc(esk1_0,esk2_0)|m1_pre_topc(X1,X2)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_20])])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (m1_pre_topc(esk1_0,esk2_0)|m1_pre_topc(X1,X2)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_19]), c_0_20])])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (m1_pre_topc(esk1_0,esk2_0)|m1_pre_topc(X1,esk2_0)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_28]), c_0_20])])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (m1_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_29]), c_0_30])])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (m1_pre_topc(X1,X2)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_31]), c_0_20])])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (~m1_pre_topc(esk1_0,esk2_0)|~m1_pre_topc(esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (m1_pre_topc(esk1_0,X1)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_32]), c_0_30])])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (~m1_pre_topc(esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_31])])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (~v1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_23])]), c_0_35])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_26]), c_0_20])])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_19]), c_0_20])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 39
% 0.19/0.38  # Proof object clause steps            : 26
% 0.19/0.38  # Proof object formula steps           : 13
% 0.19/0.38  # Proof object conjectures             : 20
% 0.19/0.38  # Proof object clause conjectures      : 17
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 10
% 0.19/0.38  # Proof object initial formulas used   : 6
% 0.19/0.38  # Proof object generating inferences   : 14
% 0.19/0.38  # Proof object simplifying inferences  : 23
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 6
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 10
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 10
% 0.19/0.38  # Processed clauses                    : 60
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 12
% 0.19/0.38  # ...remaining for further processing  : 48
% 0.19/0.38  # Other redundant clauses eliminated   : 7
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 9
% 0.19/0.38  # Backward-rewritten                   : 12
% 0.19/0.38  # Generated clauses                    : 73
% 0.19/0.38  # ...of the previous two non-trivial   : 59
% 0.19/0.38  # Contextual simplify-reflections      : 3
% 0.19/0.38  # Paramodulations                      : 59
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 14
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 17
% 0.19/0.38  #    Positive orientable unit clauses  : 3
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 3
% 0.19/0.38  #    Non-unit-clauses                  : 11
% 0.19/0.38  # Current number of unprocessed clauses: 7
% 0.19/0.38  # ...number of literals in the above   : 36
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 31
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 312
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 60
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 15
% 0.19/0.38  # Unit Clause-clause subsumption calls : 5
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 1
% 0.19/0.38  # BW rewrite match successes           : 1
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 2911
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.028 s
% 0.19/0.38  # System time              : 0.007 s
% 0.19/0.38  # Total time               : 0.035 s
% 0.19/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
