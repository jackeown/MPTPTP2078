%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:48 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 (1273 expanded)
%              Number of clauses        :   56 ( 465 expanded)
%              Number of leaves         :   12 ( 313 expanded)
%              Depth                    :   16
%              Number of atoms          :  339 (9853 expanded)
%              Number of equality atoms :   42 ( 842 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t14_tmap_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X3 = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
               => ( ( v1_tsep_1(X2,X1)
                    & m1_pre_topc(X2,X1) )
                <=> ( v1_tsep_1(X3,X1)
                    & m1_pre_topc(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tmap_1)).

fof(t60_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v3_pre_topc(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( v3_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t16_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( ( v1_tsep_1(X2,X1)
                    & m1_pre_topc(X2,X1) )
                <=> v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t12_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X2 = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
               => ( m1_pre_topc(X2,X1)
                <=> m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(fc10_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v3_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v2_pre_topc(X3)
                  & l1_pre_topc(X3) )
               => ( X3 = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                 => ( ( v1_tsep_1(X2,X1)
                      & m1_pre_topc(X2,X1) )
                  <=> ( v1_tsep_1(X3,X1)
                      & m1_pre_topc(X3,X1) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t14_tmap_1])).

fof(c_0_13,plain,(
    ! [X12,X13] :
      ( ( v3_pre_topc(X13,g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)))
        | ~ v3_pre_topc(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)))))
        | ~ v3_pre_topc(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( v3_pre_topc(X13,X12)
        | ~ v3_pre_topc(X13,g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)))))
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v3_pre_topc(X13,g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)))))
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_pre_topc])])])])).

fof(c_0_14,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & esk3_0 = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    & ( ~ v1_tsep_1(esk2_0,esk1_0)
      | ~ m1_pre_topc(esk2_0,esk1_0)
      | ~ v1_tsep_1(esk3_0,esk1_0)
      | ~ m1_pre_topc(esk3_0,esk1_0) )
    & ( v1_tsep_1(esk3_0,esk1_0)
      | v1_tsep_1(esk2_0,esk1_0) )
    & ( m1_pre_topc(esk3_0,esk1_0)
      | v1_tsep_1(esk2_0,esk1_0) )
    & ( v1_tsep_1(esk3_0,esk1_0)
      | m1_pre_topc(esk2_0,esk1_0) )
    & ( m1_pre_topc(esk3_0,esk1_0)
      | m1_pre_topc(esk2_0,esk1_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X7] : m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_16,plain,(
    ! [X6] : k2_subset_1(X6) = X6 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( esk3_0 = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X18,X19,X20] :
      ( ( ~ v1_tsep_1(X19,X18)
        | ~ m1_pre_topc(X19,X18)
        | v3_pre_topc(X20,X18)
        | X20 != u1_struct_0(X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_pre_topc(X19,X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( v1_tsep_1(X19,X18)
        | ~ v3_pre_topc(X20,X18)
        | X20 != u1_struct_0(X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_pre_topc(X19,X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( m1_pre_topc(X19,X18)
        | ~ v3_pre_topc(X20,X18)
        | X20 != u1_struct_0(X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_pre_topc(X19,X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).

fof(c_0_24,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_pre_topc(X22,X21)
      | m1_subset_1(u1_struct_0(X22),k1_zfmisc_1(u1_struct_0(X21))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_30,plain,(
    ! [X15,X16,X17] :
      ( ( ~ m1_pre_topc(X16,X15)
        | m1_pre_topc(X17,X15)
        | X16 != g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( ~ m1_pre_topc(X17,X15)
        | m1_pre_topc(X16,X15)
        | X16 != g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_tmap_1])])])])).

fof(c_0_31,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v3_pre_topc(u1_struct_0(esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_35,plain,
    ( v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | X1 != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v3_pre_topc(u1_struct_0(esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_34])).

fof(c_0_41,plain,(
    ! [X14] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v3_pre_topc(k2_struct_0(X14),X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).

fof(c_0_42,plain,(
    ! [X10] :
      ( ~ l1_struct_0(X10)
      | k2_struct_0(X10) = u1_struct_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_43,plain,(
    ! [X11] :
      ( ~ l1_pre_topc(X11)
      | l1_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_44,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | u1_struct_0(X1) != u1_struct_0(X3)
    | ~ v1_tsep_1(X3,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( v1_tsep_1(esk3_0,esk1_0)
    | v1_tsep_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_46,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_47,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_48,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0)
    | v1_tsep_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_49,negated_conjecture,
    ( m1_pre_topc(esk2_0,X1)
    | X2 != esk3_0
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_50,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0)
    | m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_51,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_52,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_53,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk2_0)
    | ~ v3_pre_topc(u1_struct_0(esk3_0),esk3_0)
    | ~ r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    | ~ v3_pre_topc(u1_struct_0(esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_26])).

cnf(c_0_55,plain,
    ( v3_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_56,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_57,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,negated_conjecture,
    ( v1_tsep_1(esk2_0,esk1_0)
    | v3_pre_topc(u1_struct_0(X1),esk1_0)
    | u1_struct_0(X1) != u1_struct_0(esk3_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_47]),c_0_52])])).

cnf(c_0_60,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk2_0)
    | ~ v3_pre_topc(u1_struct_0(esk3_0),esk3_0)
    | ~ v3_pre_topc(u1_struct_0(esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,plain,
    ( v3_pre_topc(u1_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( v1_tsep_1(esk2_0,esk1_0)
    | v3_pre_topc(u1_struct_0(esk2_0),esk1_0)
    | u1_struct_0(esk3_0) != u1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk2_0)
    | ~ v3_pre_topc(u1_struct_0(esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_51]),c_0_52])])).

cnf(c_0_64,plain,
    ( m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | X3 != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_65,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk2_0),esk1_0)
    | v3_pre_topc(u1_struct_0(X1),esk1_0)
    | u1_struct_0(esk3_0) != u1_struct_0(esk2_0)
    | u1_struct_0(X1) != u1_struct_0(esk2_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_62]),c_0_59]),c_0_46]),c_0_47])])).

cnf(c_0_66,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_61]),c_0_19]),c_0_20])])).

cnf(c_0_67,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_68,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_69,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk2_0),esk1_0)
    | v3_pre_topc(u1_struct_0(X1),esk1_0)
    | u1_struct_0(X1) != u1_struct_0(esk2_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66])])).

cnf(c_0_70,negated_conjecture,
    ( m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_18]),c_0_51]),c_0_19]),c_0_52]),c_0_20])])).

cnf(c_0_71,negated_conjecture,
    ( ~ v1_tsep_1(esk2_0,esk1_0)
    | ~ m1_pre_topc(esk2_0,esk1_0)
    | ~ v1_tsep_1(esk3_0,esk1_0)
    | ~ m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_72,plain,
    ( v1_tsep_1(X1,X2)
    | u1_struct_0(X3) != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ v3_pre_topc(u1_struct_0(X3),X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_36])).

cnf(c_0_73,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_66]),c_0_66]),c_0_59]),c_0_47])])).

cnf(c_0_74,negated_conjecture,
    ( ~ v1_tsep_1(esk2_0,esk1_0)
    | ~ v1_tsep_1(esk3_0,esk1_0)
    | ~ m1_pre_topc(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_59])])).

cnf(c_0_75,negated_conjecture,
    ( v1_tsep_1(X1,esk1_0)
    | u1_struct_0(esk2_0) != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_59]),c_0_46]),c_0_47])])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_tsep_1(esk2_0,esk1_0)
    | ~ m1_pre_topc(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_66])])).

cnf(c_0_77,negated_conjecture,
    ( m1_pre_topc(X1,X2)
    | X1 != esk3_0
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_78,negated_conjecture,
    ( ~ m1_pre_topc(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_75]),c_0_59])])).

cnf(c_0_79,negated_conjecture,
    ( m1_pre_topc(X1,esk1_0)
    | X1 != esk3_0
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_59]),c_0_47])])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_51]),c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_S5PRR_RG_S0Y
% 0.20/0.42  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.042 s
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t14_tmap_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:((v2_pre_topc(X3)&l1_pre_topc(X3))=>(X3=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>(v1_tsep_1(X3,X1)&m1_pre_topc(X3,X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_tmap_1)).
% 0.20/0.42  fof(t60_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v3_pre_topc(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))<=>(v3_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_pre_topc)).
% 0.20/0.42  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.42  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.42  fof(t16_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 0.20/0.42  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.42  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.20/0.42  fof(t12_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:((v2_pre_topc(X3)&l1_pre_topc(X3))=>(X2=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=>(m1_pre_topc(X2,X1)<=>m1_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tmap_1)).
% 0.20/0.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.42  fof(fc10_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v3_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 0.20/0.42  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.20/0.42  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.42  fof(c_0_12, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:((v2_pre_topc(X3)&l1_pre_topc(X3))=>(X3=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>(v1_tsep_1(X3,X1)&m1_pre_topc(X3,X1)))))))), inference(assume_negation,[status(cth)],[t14_tmap_1])).
% 0.20/0.42  fof(c_0_13, plain, ![X12, X13]:(((v3_pre_topc(X13,g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)))|(~v3_pre_topc(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))))|(~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)))))|(~v3_pre_topc(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))))|(~v2_pre_topc(X12)|~l1_pre_topc(X12))))&((v3_pre_topc(X13,X12)|(~v3_pre_topc(X13,g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)))|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12))))))|(~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|(~v3_pre_topc(X13,g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)))|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12))))))|(~v2_pre_topc(X12)|~l1_pre_topc(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_pre_topc])])])])).
% 0.20/0.42  fof(c_0_14, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(esk3_0=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))&((~v1_tsep_1(esk2_0,esk1_0)|~m1_pre_topc(esk2_0,esk1_0)|(~v1_tsep_1(esk3_0,esk1_0)|~m1_pre_topc(esk3_0,esk1_0)))&(((v1_tsep_1(esk3_0,esk1_0)|v1_tsep_1(esk2_0,esk1_0))&(m1_pre_topc(esk3_0,esk1_0)|v1_tsep_1(esk2_0,esk1_0)))&((v1_tsep_1(esk3_0,esk1_0)|m1_pre_topc(esk2_0,esk1_0))&(m1_pre_topc(esk3_0,esk1_0)|m1_pre_topc(esk2_0,esk1_0))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).
% 0.20/0.42  fof(c_0_15, plain, ![X7]:m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.42  fof(c_0_16, plain, ![X6]:k2_subset_1(X6)=X6, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.42  cnf(c_0_17, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.42  cnf(c_0_18, negated_conjecture, (esk3_0=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_19, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_21, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  cnf(c_0_22, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  fof(c_0_23, plain, ![X18, X19, X20]:((~v1_tsep_1(X19,X18)|~m1_pre_topc(X19,X18)|v3_pre_topc(X20,X18)|X20!=u1_struct_0(X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|~m1_pre_topc(X19,X18)|(~v2_pre_topc(X18)|~l1_pre_topc(X18)))&((v1_tsep_1(X19,X18)|~v3_pre_topc(X20,X18)|X20!=u1_struct_0(X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|~m1_pre_topc(X19,X18)|(~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(m1_pre_topc(X19,X18)|~v3_pre_topc(X20,X18)|X20!=u1_struct_0(X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|~m1_pre_topc(X19,X18)|(~v2_pre_topc(X18)|~l1_pre_topc(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).
% 0.20/0.42  fof(c_0_24, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.42  cnf(c_0_25, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v3_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])])).
% 0.20/0.42  cnf(c_0_26, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.42  cnf(c_0_27, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.42  cnf(c_0_28, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  fof(c_0_29, plain, ![X21, X22]:(~l1_pre_topc(X21)|(~m1_pre_topc(X22,X21)|m1_subset_1(u1_struct_0(X22),k1_zfmisc_1(u1_struct_0(X21))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.20/0.42  fof(c_0_30, plain, ![X15, X16, X17]:((~m1_pre_topc(X16,X15)|m1_pre_topc(X17,X15)|X16!=g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))|(~v2_pre_topc(X17)|~l1_pre_topc(X17))|(~v2_pre_topc(X16)|~l1_pre_topc(X16))|~l1_pre_topc(X15))&(~m1_pre_topc(X17,X15)|m1_pre_topc(X16,X15)|X16!=g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))|(~v2_pre_topc(X17)|~l1_pre_topc(X17))|(~v2_pre_topc(X16)|~l1_pre_topc(X16))|~l1_pre_topc(X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_tmap_1])])])])).
% 0.20/0.42  fof(c_0_31, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.42  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.42  cnf(c_0_33, negated_conjecture, (m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~v3_pre_topc(u1_struct_0(esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.42  cnf(c_0_34, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_18]), c_0_19]), c_0_20])])).
% 0.20/0.42  cnf(c_0_35, plain, (v3_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_pre_topc(X1,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[c_0_28])).
% 0.20/0.42  cnf(c_0_36, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.42  cnf(c_0_37, plain, (m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)|X1!=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.42  cnf(c_0_38, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.42  cnf(c_0_39, negated_conjecture, (r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v3_pre_topc(u1_struct_0(esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.42  cnf(c_0_40, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk3_0))|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_32, c_0_34])).
% 0.20/0.42  fof(c_0_41, plain, ![X14]:(~v2_pre_topc(X14)|~l1_pre_topc(X14)|v3_pre_topc(k2_struct_0(X14),X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_tops_1])])).
% 0.20/0.42  fof(c_0_42, plain, ![X10]:(~l1_struct_0(X10)|k2_struct_0(X10)=u1_struct_0(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.20/0.42  fof(c_0_43, plain, ![X11]:(~l1_pre_topc(X11)|l1_struct_0(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.42  cnf(c_0_44, plain, (v3_pre_topc(u1_struct_0(X1),X2)|u1_struct_0(X1)!=u1_struct_0(X3)|~v1_tsep_1(X3,X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.42  cnf(c_0_45, negated_conjecture, (v1_tsep_1(esk3_0,esk1_0)|v1_tsep_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_46, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_47, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_48, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)|v1_tsep_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_49, negated_conjecture, (m1_pre_topc(esk2_0,X1)|X2!=esk3_0|~m1_pre_topc(X2,X1)|~v2_pre_topc(X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_18]), c_0_19]), c_0_20])])).
% 0.20/0.42  cnf(c_0_50, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)|m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_51, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_52, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_53, negated_conjecture, (u1_struct_0(esk3_0)=u1_struct_0(esk2_0)|~v3_pre_topc(u1_struct_0(esk3_0),esk3_0)|~r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.42  cnf(c_0_54, negated_conjecture, (r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk3_0))|~v3_pre_topc(u1_struct_0(esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_40, c_0_26])).
% 0.20/0.42  cnf(c_0_55, plain, (v3_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.42  cnf(c_0_56, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.42  cnf(c_0_57, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.42  cnf(c_0_58, negated_conjecture, (v1_tsep_1(esk2_0,esk1_0)|v3_pre_topc(u1_struct_0(X1),esk1_0)|u1_struct_0(X1)!=u1_struct_0(esk3_0)|~m1_pre_topc(X1,esk1_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47])]), c_0_48])).
% 0.20/0.42  cnf(c_0_59, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_47]), c_0_52])])).
% 0.20/0.42  cnf(c_0_60, negated_conjecture, (u1_struct_0(esk3_0)=u1_struct_0(esk2_0)|~v3_pre_topc(u1_struct_0(esk3_0),esk3_0)|~v3_pre_topc(u1_struct_0(esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.42  cnf(c_0_61, plain, (v3_pre_topc(u1_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 0.20/0.42  cnf(c_0_62, negated_conjecture, (v1_tsep_1(esk2_0,esk1_0)|v3_pre_topc(u1_struct_0(esk2_0),esk1_0)|u1_struct_0(esk3_0)!=u1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.42  cnf(c_0_63, negated_conjecture, (u1_struct_0(esk3_0)=u1_struct_0(esk2_0)|~v3_pre_topc(u1_struct_0(esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_51]), c_0_52])])).
% 0.20/0.42  cnf(c_0_64, plain, (m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)|X3!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.42  cnf(c_0_65, negated_conjecture, (v3_pre_topc(u1_struct_0(esk2_0),esk1_0)|v3_pre_topc(u1_struct_0(X1),esk1_0)|u1_struct_0(esk3_0)!=u1_struct_0(esk2_0)|u1_struct_0(X1)!=u1_struct_0(esk2_0)|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_62]), c_0_59]), c_0_46]), c_0_47])])).
% 0.20/0.42  cnf(c_0_66, negated_conjecture, (u1_struct_0(esk3_0)=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_61]), c_0_19]), c_0_20])])).
% 0.20/0.42  cnf(c_0_67, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_pre_topc(X1,X2)|~v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(er,[status(thm)],[c_0_64])).
% 0.20/0.42  cnf(c_0_68, plain, (v1_tsep_1(X1,X2)|~v3_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  cnf(c_0_69, negated_conjecture, (v3_pre_topc(u1_struct_0(esk2_0),esk1_0)|v3_pre_topc(u1_struct_0(X1),esk1_0)|u1_struct_0(X1)!=u1_struct_0(esk2_0)|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66])])).
% 0.20/0.42  cnf(c_0_70, negated_conjecture, (m1_pre_topc(esk3_0,X1)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_18]), c_0_51]), c_0_19]), c_0_52]), c_0_20])])).
% 0.20/0.42  cnf(c_0_71, negated_conjecture, (~v1_tsep_1(esk2_0,esk1_0)|~m1_pre_topc(esk2_0,esk1_0)|~v1_tsep_1(esk3_0,esk1_0)|~m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_72, plain, (v1_tsep_1(X1,X2)|u1_struct_0(X3)!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X3,X2)|~v3_pre_topc(u1_struct_0(X3),X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_68, c_0_36])).
% 0.20/0.42  cnf(c_0_73, negated_conjecture, (v3_pre_topc(u1_struct_0(esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_66]), c_0_66]), c_0_59]), c_0_47])])).
% 0.20/0.42  cnf(c_0_74, negated_conjecture, (~v1_tsep_1(esk2_0,esk1_0)|~v1_tsep_1(esk3_0,esk1_0)|~m1_pre_topc(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_59])])).
% 0.20/0.42  cnf(c_0_75, negated_conjecture, (v1_tsep_1(X1,esk1_0)|u1_struct_0(esk2_0)!=u1_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_59]), c_0_46]), c_0_47])])).
% 0.20/0.42  cnf(c_0_76, negated_conjecture, (~v1_tsep_1(esk2_0,esk1_0)|~m1_pre_topc(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_66])])).
% 0.20/0.42  cnf(c_0_77, negated_conjecture, (m1_pre_topc(X1,X2)|X1!=esk3_0|~m1_pre_topc(esk2_0,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_18]), c_0_19]), c_0_20])])).
% 0.20/0.42  cnf(c_0_78, negated_conjecture, (~m1_pre_topc(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_75]), c_0_59])])).
% 0.20/0.42  cnf(c_0_79, negated_conjecture, (m1_pre_topc(X1,esk1_0)|X1!=esk3_0|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_59]), c_0_47])])).
% 0.20/0.42  cnf(c_0_80, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_51]), c_0_52])]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 81
% 0.20/0.42  # Proof object clause steps            : 56
% 0.20/0.42  # Proof object formula steps           : 25
% 0.20/0.42  # Proof object conjectures             : 39
% 0.20/0.42  # Proof object clause conjectures      : 36
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 25
% 0.20/0.42  # Proof object initial formulas used   : 12
% 0.20/0.42  # Proof object generating inferences   : 27
% 0.20/0.42  # Proof object simplifying inferences  : 60
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 12
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 32
% 0.20/0.42  # Removed in clause preprocessing      : 2
% 0.20/0.42  # Initial clauses in saturation        : 30
% 0.20/0.42  # Processed clauses                    : 207
% 0.20/0.42  # ...of these trivial                  : 7
% 0.20/0.42  # ...subsumed                          : 57
% 0.20/0.42  # ...remaining for further processing  : 143
% 0.20/0.42  # Other redundant clauses eliminated   : 2
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 8
% 0.20/0.42  # Backward-rewritten                   : 39
% 0.20/0.42  # Generated clauses                    : 347
% 0.20/0.42  # ...of the previous two non-trivial   : 313
% 0.20/0.42  # Contextual simplify-reflections      : 5
% 0.20/0.42  # Paramodulations                      : 341
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 5
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 93
% 0.20/0.42  #    Positive orientable unit clauses  : 14
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 4
% 0.20/0.42  #    Non-unit-clauses                  : 75
% 0.20/0.42  # Current number of unprocessed clauses: 116
% 0.20/0.42  # ...number of literals in the above   : 646
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 49
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 3676
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 736
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 59
% 0.20/0.42  # Unit Clause-clause subsumption calls : 56
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 8
% 0.20/0.42  # BW rewrite match successes           : 5
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 11245
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.072 s
% 0.20/0.42  # System time              : 0.007 s
% 0.20/0.42  # Total time               : 0.079 s
% 0.20/0.42  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
