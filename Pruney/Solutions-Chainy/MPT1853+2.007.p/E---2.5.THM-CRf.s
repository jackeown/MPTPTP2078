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
% DateTime   : Thu Dec  3 11:19:26 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 240 expanded)
%              Number of clauses        :   26 (  80 expanded)
%              Number of leaves         :    8 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  189 (1126 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v1_tex_2(k1_tex_2(X1,X2),X1)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(dt_k1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2))
        & m1_pre_topc(k1_tex_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(cc13_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & ~ v7_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( ( ~ v2_struct_0(X2)
              & ~ v1_tex_2(X2,X1) )
           => ( ~ v2_struct_0(X2)
              & ~ v7_struct_0(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc13_tex_2)).

fof(t8_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
              & v7_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

fof(fc2_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v7_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(cc10_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v7_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( ~ v2_struct_0(X2)
           => ( ~ v2_struct_0(X2)
              & ~ v1_tex_2(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).

fof(t9_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & ~ v7_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tex_2)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v1_tex_2(k1_tex_2(X1,X2),X1)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_tex_2])).

fof(c_0_9,plain,(
    ! [X8,X9] :
      ( ( ~ v2_struct_0(k1_tex_2(X8,X9))
        | v2_struct_0(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8)) )
      & ( v1_pre_topc(k1_tex_2(X8,X9))
        | v2_struct_0(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8)) )
      & ( m1_pre_topc(k1_tex_2(X8,X9),X8)
        | v2_struct_0(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & ( ~ v1_tex_2(k1_tex_2(esk1_0,esk2_0),esk1_0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) )
    & ( v1_tex_2(k1_tex_2(esk1_0,esk2_0),esk1_0)
      | v1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X6,X7] :
      ( ( ~ v2_struct_0(X7)
        | v2_struct_0(X7)
        | v1_tex_2(X7,X6)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X6)
        | v7_struct_0(X6)
        | ~ l1_pre_topc(X6) )
      & ( ~ v7_struct_0(X7)
        | v2_struct_0(X7)
        | v1_tex_2(X7,X6)
        | ~ m1_pre_topc(X7,X6)
        | v2_struct_0(X6)
        | v7_struct_0(X6)
        | ~ l1_pre_topc(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc13_tex_2])])])])])).

cnf(c_0_12,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X12,X13] :
      ( v2_struct_0(X12)
      | ~ l1_struct_0(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X12),X13),u1_struct_0(X12))
      | ~ v7_struct_0(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | v1_tex_2(X1,X2)
    | v2_struct_0(X2)
    | v7_struct_0(X2)
    | ~ v7_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( m1_pre_topc(k1_tex_2(esk1_0,esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])]),c_0_15])).

fof(c_0_19,plain,(
    ! [X10,X11] :
      ( ( ~ v2_struct_0(k1_tex_2(X10,X11))
        | v2_struct_0(X10)
        | ~ l1_pre_topc(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10)) )
      & ( v7_struct_0(k1_tex_2(X10,X11))
        | v2_struct_0(X10)
        | ~ l1_pre_topc(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10)) )
      & ( v1_pre_topc(k1_tex_2(X10,X11))
        | v2_struct_0(X10)
        | ~ l1_pre_topc(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
    | ~ v7_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk1_0,esk2_0),esk1_0)
    | v1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk1_0,esk2_0),esk1_0)
    | v7_struct_0(esk1_0)
    | v2_struct_0(k1_tex_2(esk1_0,esk2_0))
    | ~ v7_struct_0(k1_tex_2(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_14])]),c_0_15])).

cnf(c_0_23,plain,
    ( v7_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk1_0,esk2_0),esk1_0)
    | ~ v7_struct_0(esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_13])]),c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk1_0,esk2_0),esk1_0)
    | v7_struct_0(esk1_0)
    | v2_struct_0(k1_tex_2(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk1_0,esk2_0),esk1_0)
    | v2_struct_0(k1_tex_2(esk1_0,esk2_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_28,plain,(
    ! [X3] :
      ( ~ l1_pre_topc(X3)
      | l1_struct_0(X3) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_29,plain,(
    ! [X4,X5] :
      ( ( ~ v2_struct_0(X5)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X4)
        | ~ v7_struct_0(X4)
        | ~ l1_pre_topc(X4) )
      & ( ~ v1_tex_2(X5,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X4)
        | ~ v7_struct_0(X4)
        | ~ l1_pre_topc(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc10_tex_2])])])])])).

cnf(c_0_30,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk1_0,esk2_0),esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_31,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_32,plain,(
    ! [X14,X15] :
      ( v2_struct_0(X14)
      | v7_struct_0(X14)
      | ~ l1_struct_0(X14)
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | v1_subset_1(k6_domain_1(u1_struct_0(X14),X15),u1_struct_0(X14)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_tex_2])])])])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v7_struct_0(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( v1_tex_2(k1_tex_2(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_14])])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(X1)
    | v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(esk1_0,esk2_0),esk1_0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk1_0,esk2_0))
    | ~ v7_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_18]),c_0_14])]),c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))
    | v7_struct_0(esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_13]),c_0_15])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_34])])).

cnf(c_0_40,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk1_0,esk2_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_41,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_40]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_31]),c_0_14])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.32  % Computer   : n014.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 09:21:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.36  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S033N
% 0.19/0.36  # and selection function PSelectUnlessUniqMax.
% 0.19/0.36  #
% 0.19/0.36  # Preprocessing time       : 0.029 s
% 0.19/0.36  # Presaturation interreduction done
% 0.19/0.36  
% 0.19/0.36  # Proof found!
% 0.19/0.36  # SZS status Theorem
% 0.19/0.36  # SZS output start CNFRefutation
% 0.19/0.36  fof(t20_tex_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 0.19/0.36  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.19/0.36  fof(cc13_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&~(v7_struct_0(X1)))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((~(v2_struct_0(X2))&~(v1_tex_2(X2,X1)))=>(~(v2_struct_0(X2))&~(v7_struct_0(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc13_tex_2)).
% 0.19/0.36  fof(t8_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~((v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))&v7_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 0.19/0.36  fof(fc2_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v7_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 0.19/0.36  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.36  fof(cc10_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v7_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>(~(v2_struct_0(X2))=>(~(v2_struct_0(X2))&~(v1_tex_2(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc10_tex_2)).
% 0.19/0.36  fof(t9_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&~(v7_struct_0(X1)))&l1_struct_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_tex_2)).
% 0.19/0.36  fof(c_0_8, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v1_tex_2(k1_tex_2(X1,X2),X1)<=>v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1)))))), inference(assume_negation,[status(cth)],[t20_tex_2])).
% 0.19/0.36  fof(c_0_9, plain, ![X8, X9]:(((~v2_struct_0(k1_tex_2(X8,X9))|(v2_struct_0(X8)|~l1_pre_topc(X8)|~m1_subset_1(X9,u1_struct_0(X8))))&(v1_pre_topc(k1_tex_2(X8,X9))|(v2_struct_0(X8)|~l1_pre_topc(X8)|~m1_subset_1(X9,u1_struct_0(X8)))))&(m1_pre_topc(k1_tex_2(X8,X9),X8)|(v2_struct_0(X8)|~l1_pre_topc(X8)|~m1_subset_1(X9,u1_struct_0(X8))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.19/0.36  fof(c_0_10, negated_conjecture, ((~v2_struct_0(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&((~v1_tex_2(k1_tex_2(esk1_0,esk2_0),esk1_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)))&(v1_tex_2(k1_tex_2(esk1_0,esk2_0),esk1_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.19/0.36  fof(c_0_11, plain, ![X6, X7]:((~v2_struct_0(X7)|(v2_struct_0(X7)|v1_tex_2(X7,X6))|~m1_pre_topc(X7,X6)|(v2_struct_0(X6)|v7_struct_0(X6)|~l1_pre_topc(X6)))&(~v7_struct_0(X7)|(v2_struct_0(X7)|v1_tex_2(X7,X6))|~m1_pre_topc(X7,X6)|(v2_struct_0(X6)|v7_struct_0(X6)|~l1_pre_topc(X6)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc13_tex_2])])])])])).
% 0.19/0.36  cnf(c_0_12, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.36  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.36  cnf(c_0_14, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.36  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.36  fof(c_0_16, plain, ![X12, X13]:(v2_struct_0(X12)|~l1_struct_0(X12)|(~m1_subset_1(X13,u1_struct_0(X12))|(~v1_subset_1(k6_domain_1(u1_struct_0(X12),X13),u1_struct_0(X12))|~v7_struct_0(X12)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_tex_2])])])])).
% 0.19/0.36  cnf(c_0_17, plain, (v2_struct_0(X1)|v1_tex_2(X1,X2)|v2_struct_0(X2)|v7_struct_0(X2)|~v7_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.36  cnf(c_0_18, negated_conjecture, (m1_pre_topc(k1_tex_2(esk1_0,esk2_0),esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])]), c_0_15])).
% 0.19/0.36  fof(c_0_19, plain, ![X10, X11]:(((~v2_struct_0(k1_tex_2(X10,X11))|(v2_struct_0(X10)|~l1_pre_topc(X10)|~m1_subset_1(X11,u1_struct_0(X10))))&(v7_struct_0(k1_tex_2(X10,X11))|(v2_struct_0(X10)|~l1_pre_topc(X10)|~m1_subset_1(X11,u1_struct_0(X10)))))&(v1_pre_topc(k1_tex_2(X10,X11))|(v2_struct_0(X10)|~l1_pre_topc(X10)|~m1_subset_1(X11,u1_struct_0(X10))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).
% 0.19/0.36  cnf(c_0_20, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))|~v7_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.36  cnf(c_0_21, negated_conjecture, (v1_tex_2(k1_tex_2(esk1_0,esk2_0),esk1_0)|v1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.36  cnf(c_0_22, negated_conjecture, (v1_tex_2(k1_tex_2(esk1_0,esk2_0),esk1_0)|v7_struct_0(esk1_0)|v2_struct_0(k1_tex_2(esk1_0,esk2_0))|~v7_struct_0(k1_tex_2(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_14])]), c_0_15])).
% 0.19/0.36  cnf(c_0_23, plain, (v7_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.36  cnf(c_0_24, negated_conjecture, (v1_tex_2(k1_tex_2(esk1_0,esk2_0),esk1_0)|~v7_struct_0(esk1_0)|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_13])]), c_0_15])).
% 0.19/0.36  cnf(c_0_25, negated_conjecture, (v1_tex_2(k1_tex_2(esk1_0,esk2_0),esk1_0)|v7_struct_0(esk1_0)|v2_struct_0(k1_tex_2(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_13]), c_0_14])]), c_0_15])).
% 0.19/0.36  cnf(c_0_26, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.36  cnf(c_0_27, negated_conjecture, (v1_tex_2(k1_tex_2(esk1_0,esk2_0),esk1_0)|v2_struct_0(k1_tex_2(esk1_0,esk2_0))|~l1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.36  fof(c_0_28, plain, ![X3]:(~l1_pre_topc(X3)|l1_struct_0(X3)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.36  fof(c_0_29, plain, ![X4, X5]:((~v2_struct_0(X5)|v2_struct_0(X5)|~m1_pre_topc(X5,X4)|(v2_struct_0(X4)|~v7_struct_0(X4)|~l1_pre_topc(X4)))&(~v1_tex_2(X5,X4)|v2_struct_0(X5)|~m1_pre_topc(X5,X4)|(v2_struct_0(X4)|~v7_struct_0(X4)|~l1_pre_topc(X4)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc10_tex_2])])])])])).
% 0.19/0.36  cnf(c_0_30, negated_conjecture, (v1_tex_2(k1_tex_2(esk1_0,esk2_0),esk1_0)|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_13]), c_0_14])]), c_0_15])).
% 0.19/0.36  cnf(c_0_31, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.36  fof(c_0_32, plain, ![X14, X15]:(v2_struct_0(X14)|v7_struct_0(X14)|~l1_struct_0(X14)|(~m1_subset_1(X15,u1_struct_0(X14))|v1_subset_1(k6_domain_1(u1_struct_0(X14),X15),u1_struct_0(X14)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_tex_2])])])])).
% 0.19/0.36  cnf(c_0_33, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~v7_struct_0(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.36  cnf(c_0_34, negated_conjecture, (v1_tex_2(k1_tex_2(esk1_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_14])])).
% 0.19/0.36  cnf(c_0_35, plain, (v2_struct_0(X1)|v7_struct_0(X1)|v1_subset_1(k6_domain_1(u1_struct_0(X1),X2),u1_struct_0(X1))|~l1_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.36  cnf(c_0_36, negated_conjecture, (~v1_tex_2(k1_tex_2(esk1_0,esk2_0),esk1_0)|~v1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.36  cnf(c_0_37, negated_conjecture, (v2_struct_0(k1_tex_2(esk1_0,esk2_0))|~v7_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_18]), c_0_14])]), c_0_15])).
% 0.19/0.36  cnf(c_0_38, negated_conjecture, (v1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))|v7_struct_0(esk1_0)|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_13]), c_0_15])).
% 0.19/0.36  cnf(c_0_39, negated_conjecture, (~v1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_34])])).
% 0.19/0.36  cnf(c_0_40, negated_conjecture, (v2_struct_0(k1_tex_2(esk1_0,esk2_0))|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.19/0.36  cnf(c_0_41, negated_conjecture, (~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_40]), c_0_13]), c_0_14])]), c_0_15])).
% 0.19/0.36  cnf(c_0_42, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_31]), c_0_14])]), ['proof']).
% 0.19/0.36  # SZS output end CNFRefutation
% 0.19/0.36  # Proof object total steps             : 43
% 0.19/0.36  # Proof object clause steps            : 26
% 0.19/0.36  # Proof object formula steps           : 17
% 0.19/0.36  # Proof object conjectures             : 21
% 0.19/0.36  # Proof object clause conjectures      : 18
% 0.19/0.36  # Proof object formula conjectures     : 3
% 0.19/0.36  # Proof object initial clauses used    : 13
% 0.19/0.36  # Proof object initial formulas used   : 8
% 0.19/0.36  # Proof object generating inferences   : 12
% 0.19/0.36  # Proof object simplifying inferences  : 33
% 0.19/0.36  # Training examples: 0 positive, 0 negative
% 0.19/0.36  # Parsed axioms                        : 8
% 0.19/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.36  # Initial clauses                      : 18
% 0.19/0.36  # Removed in clause preprocessing      : 2
% 0.19/0.36  # Initial clauses in saturation        : 16
% 0.19/0.36  # Processed clauses                    : 51
% 0.19/0.36  # ...of these trivial                  : 0
% 0.19/0.36  # ...subsumed                          : 5
% 0.19/0.36  # ...remaining for further processing  : 46
% 0.19/0.36  # Other redundant clauses eliminated   : 0
% 0.19/0.36  # Clauses deleted for lack of memory   : 0
% 0.19/0.36  # Backward-subsumed                    : 4
% 0.19/0.36  # Backward-rewritten                   : 5
% 0.19/0.36  # Generated clauses                    : 25
% 0.19/0.36  # ...of the previous two non-trivial   : 25
% 0.19/0.36  # Contextual simplify-reflections      : 1
% 0.19/0.36  # Paramodulations                      : 23
% 0.19/0.36  # Factorizations                       : 2
% 0.19/0.36  # Equation resolutions                 : 0
% 0.19/0.36  # Propositional unsat checks           : 0
% 0.19/0.36  #    Propositional check models        : 0
% 0.19/0.36  #    Propositional check unsatisfiable : 0
% 0.19/0.36  #    Propositional clauses             : 0
% 0.19/0.36  #    Propositional clauses after purity: 0
% 0.19/0.36  #    Propositional unsat core size     : 0
% 0.19/0.36  #    Propositional preprocessing time  : 0.000
% 0.19/0.36  #    Propositional encoding time       : 0.000
% 0.19/0.36  #    Propositional solver time         : 0.000
% 0.19/0.36  #    Success case prop preproc time    : 0.000
% 0.19/0.36  #    Success case prop encoding time   : 0.000
% 0.19/0.36  #    Success case prop solver time     : 0.000
% 0.19/0.36  # Current number of processed clauses  : 23
% 0.19/0.36  #    Positive orientable unit clauses  : 4
% 0.19/0.36  #    Positive unorientable unit clauses: 0
% 0.19/0.36  #    Negative unit clauses             : 3
% 0.19/0.36  #    Non-unit-clauses                  : 16
% 0.19/0.36  # Current number of unprocessed clauses: 2
% 0.19/0.36  # ...number of literals in the above   : 4
% 0.19/0.36  # Current number of archived formulas  : 0
% 0.19/0.36  # Current number of archived clauses   : 23
% 0.19/0.36  # Clause-clause subsumption calls (NU) : 78
% 0.19/0.36  # Rec. Clause-clause subsumption calls : 25
% 0.19/0.36  # Non-unit clause-clause subsumptions  : 10
% 0.19/0.36  # Unit Clause-clause subsumption calls : 5
% 0.19/0.36  # Rewrite failures with RHS unbound    : 0
% 0.19/0.36  # BW rewrite match attempts            : 1
% 0.19/0.36  # BW rewrite match successes           : 1
% 0.19/0.36  # Condensation attempts                : 0
% 0.19/0.36  # Condensation successes               : 0
% 0.19/0.36  # Termbank termtop insertions          : 2231
% 0.19/0.36  
% 0.19/0.36  # -------------------------------------------------
% 0.19/0.36  # User time                : 0.029 s
% 0.19/0.36  # System time              : 0.005 s
% 0.19/0.36  # Total time               : 0.035 s
% 0.19/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
