%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:18 EST 2020

% Result     : Theorem 0.56s
% Output     : CNFRefutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :  119 (43448 expanded)
%              Number of clauses        :   98 (19076 expanded)
%              Number of leaves         :   10 (11370 expanded)
%              Depth                    :   38
%              Number of atoms          :  428 (166301 expanded)
%              Number of equality atoms :   84 (26429 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

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

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(t66_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
             => ( X2 = X3
               => g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X2)),u1_pre_topc(k1_pre_topc(X1,X2))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(t33_compts_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_compts_1(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( v2_compts_1(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_compts_1)).

fof(t12_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( X2 = k1_xboole_0
             => ( v2_compts_1(X2,X1)
              <=> v1_compts_1(k1_pre_topc(X1,X2)) ) )
            & ( v2_pre_topc(X1)
             => ( X2 = k1_xboole_0
                | ( v2_compts_1(X2,X1)
                <=> v1_compts_1(k1_pre_topc(X1,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_compts_1)).

fof(fc6_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(c_0_10,plain,(
    ! [X14,X15,X16,X17] :
      ( ( X14 = X16
        | g1_pre_topc(X14,X15) != g1_pre_topc(X16,X17)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))) )
      & ( X15 = X17
        | g1_pre_topc(X14,X15) != g1_pre_topc(X16,X17)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_11,plain,(
    ! [X12] :
      ( ~ l1_pre_topc(X12)
      | m1_subset_1(u1_pre_topc(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_12,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | ~ v1_pre_topc(X5)
      | X5 = g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_15,plain,
    ( u1_pre_topc(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X6,X7] :
      ( ( v1_pre_topc(g1_pre_topc(X6,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X6))) )
      & ( l1_pre_topc(g1_pre_topc(X6,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X6))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

cnf(c_0_18,plain,
    ( u1_pre_topc(g1_pre_topc(X1,X2)) = X2
    | ~ v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ l1_pre_topc(g1_pre_topc(X1,X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16])])).

cnf(c_0_19,plain,
    ( v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( u1_pre_topc(g1_pre_topc(X1,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_22,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(X2,X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_21]),c_0_20])).

fof(c_0_24,plain,(
    ! [X18,X19,X20] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))))
      | X19 != X20
      | g1_pre_topc(u1_struct_0(k1_pre_topc(X18,X19)),u1_pre_topc(k1_pre_topc(X18,X19))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)),X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t66_pre_topc])])])).

fof(c_0_25,plain,(
    ! [X10,X11] :
      ( ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(X11,X10)
      | l1_pre_topc(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_26,plain,(
    ! [X8,X9] :
      ( ( v1_pre_topc(k1_pre_topc(X8,X9))
        | ~ l1_pre_topc(X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8))) )
      & ( m1_pre_topc(k1_pre_topc(X8,X9),X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

cnf(c_0_27,plain,
    ( u1_struct_0(g1_pre_topc(X1,X2)) = X3
    | g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2) != g1_pre_topc(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2) = g1_pre_topc(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_21]),c_0_20]),c_0_19])).

cnf(c_0_29,plain,
    ( u1_struct_0(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_13])).

cnf(c_0_30,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X2)),u1_pre_topc(k1_pre_topc(X1,X2))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | X2 != X3 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( u1_struct_0(g1_pre_topc(X1,X2)) = X3
    | g1_pre_topc(X1,X2) != g1_pre_topc(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( u1_struct_0(g1_pre_topc(X1,X2)) = X1
    | ~ v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ l1_pre_topc(g1_pre_topc(X1,X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_16])])).

fof(c_0_35,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v2_compts_1(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          <=> ( v2_compts_1(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_compts_1])).

cnf(c_0_36,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X2)),u1_pre_topc(k1_pre_topc(X1,X2))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( l1_pre_topc(k1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( v1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_13])).

cnf(c_0_40,plain,
    ( u1_struct_0(g1_pre_topc(X1,X2)) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_19]),c_0_20])).

fof(c_0_41,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ( ~ v2_compts_1(esk2_0,esk1_0)
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      | ~ v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) )
    & ( v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
      | v2_compts_1(esk2_0,esk1_0) )
    & ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
      | v2_compts_1(esk2_0,esk1_0) )
    & ( v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
      | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) )
    & ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
      | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_35])])])])])).

cnf(c_0_42,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) = k1_pre_topc(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_43,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_struct_0(k1_pre_topc(X2,X3))
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_36])).

cnf(c_0_44,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2),X3) = k1_pre_topc(g1_pre_topc(X1,X2),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_21]),c_0_20])).

cnf(c_0_48,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_struct_0(k1_pre_topc(X2,X3))
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_44]),c_0_46])])).

cnf(c_0_50,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(X1,X2),X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_47])).

cnf(c_0_51,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2)) = u1_struct_0(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_23])).

cnf(c_0_52,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_struct_0(k1_pre_topc(esk1_0,esk2_0))
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_46])])).

cnf(c_0_53,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(X1,X2),X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,plain,
    ( l1_pre_topc(k1_pre_topc(g1_pre_topc(X1,X2),X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)) = u1_struct_0(k1_pre_topc(esk1_0,esk2_0))
    | ~ v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))
    | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_16])])).

cnf(c_0_56,plain,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_44]),c_0_20]),c_0_13])).

cnf(c_0_57,plain,
    ( l1_pre_topc(k1_pre_topc(g1_pre_topc(X1,X2),X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)) = u1_struct_0(k1_pre_topc(esk1_0,esk2_0))
    | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_49]),c_0_46])])).

cnf(c_0_59,plain,
    ( l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_44]),c_0_20]),c_0_13])).

fof(c_0_60,plain,(
    ! [X21,X22] :
      ( ( ~ v2_compts_1(X22,X21)
        | v1_compts_1(k1_pre_topc(X21,X22))
        | X22 != k1_xboole_0
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_pre_topc(X21) )
      & ( ~ v1_compts_1(k1_pre_topc(X21,X22))
        | v2_compts_1(X22,X21)
        | X22 != k1_xboole_0
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_pre_topc(X21) )
      & ( ~ v2_compts_1(X22,X21)
        | v1_compts_1(k1_pre_topc(X21,X22))
        | X22 = k1_xboole_0
        | ~ v2_pre_topc(X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_pre_topc(X21) )
      & ( ~ v1_compts_1(k1_pre_topc(X21,X22))
        | v2_compts_1(X22,X21)
        | X22 = k1_xboole_0
        | ~ v2_pre_topc(X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_compts_1])])])])).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)) = u1_struct_0(k1_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_49]),c_0_46])])).

cnf(c_0_62,plain,
    ( u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)) = u1_pre_topc(k1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))
    | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_36])).

cnf(c_0_63,plain,
    ( v1_compts_1(k1_pre_topc(X2,X1))
    | X1 = k1_xboole_0
    | ~ v2_compts_1(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | v2_compts_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_65,negated_conjecture,
    ( v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | v2_compts_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_66,plain,(
    ! [X13] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( v2_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)))))
    | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_61])).

cnf(c_0_68,plain,
    ( u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)) = u1_pre_topc(k1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_38]),c_0_37])).

cnf(c_0_69,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))
    | v2_compts_1(esk2_0,esk1_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_70,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_72,plain,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_44])).

cnf(c_0_73,plain,
    ( u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)) = u1_pre_topc(k1_pre_topc(X1,X2))
    | ~ m1_subset_1(u1_pre_topc(k1_pre_topc(X1,X2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_36])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(k1_pre_topc(esk1_0,esk2_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)))))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_49]),c_0_46])]),c_0_37])).

cnf(c_0_75,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))
    | v2_compts_1(esk2_0,esk1_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_46])])).

cnf(c_0_76,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X2)),u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_36]),c_0_37]),c_0_59]),c_0_56])).

cnf(c_0_77,negated_conjecture,
    ( u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)) = u1_pre_topc(k1_pre_topc(esk1_0,esk2_0))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_49]),c_0_46])])).

cnf(c_0_78,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))
    | v2_compts_1(esk2_0,esk1_0)
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_20])).

cnf(c_0_79,plain,
    ( v2_compts_1(X2,X1)
    | X2 = k1_xboole_0
    | ~ v1_compts_1(k1_pre_topc(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_80,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)),u1_pre_topc(k1_pre_topc(esk1_0,esk2_0))) = k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_49]),c_0_46])])).

cnf(c_0_81,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X2)),u1_pre_topc(k1_pre_topc(X1,X2))) = k1_pre_topc(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_42])).

cnf(c_0_82,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))
    | v2_compts_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_13]),c_0_46])])).

cnf(c_0_83,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(esk1_0,esk2_0))
    | ~ v2_compts_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_49]),c_0_71]),c_0_46])])).

cnf(c_0_84,plain,
    ( X1 = k1_xboole_0
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_79,c_0_44])).

cnf(c_0_85,negated_conjecture,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0) = k1_pre_topc(esk1_0,esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_49]),c_0_46])])).

cnf(c_0_86,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_compts_1(k1_pre_topc(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_42]),c_0_49]),c_0_46])]),c_0_64]),c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_49]),c_0_46])]),c_0_86])).

cnf(c_0_88,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_70]),c_0_71]),c_0_46])])).

cnf(c_0_89,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_20])).

cnf(c_0_90,negated_conjecture,
    ( ~ v2_compts_1(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_91,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_13]),c_0_46])])).

cnf(c_0_92,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v2_compts_1(esk2_0,esk1_0)
    | ~ v1_compts_1(k1_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_49]),c_0_71]),c_0_46])])).

cnf(c_0_93,negated_conjecture,
    ( ~ v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v2_compts_1(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_49])])).

cnf(c_0_94,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_44]),c_0_49]),c_0_46])])).

cnf(c_0_95,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v2_compts_1(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_86])).

cnf(c_0_96,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95])).

cnf(c_0_97,plain,
    ( v2_compts_1(X2,X1)
    | ~ v1_compts_1(k1_pre_topc(X1,X2))
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_98,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_44]),c_0_49]),c_0_46])])).

cnf(c_0_99,plain,
    ( v2_compts_1(k1_xboole_0,X1)
    | ~ v1_compts_1(k1_pre_topc(X1,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_97])).

cnf(c_0_100,negated_conjecture,
    ( ~ v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v2_compts_1(k1_xboole_0,esk1_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_98]),c_0_98]),c_0_98])).

cnf(c_0_101,plain,
    ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v1_compts_1(k1_pre_topc(X1,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_42])).

cnf(c_0_102,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_49,c_0_98])).

cnf(c_0_103,plain,
    ( v1_compts_1(k1_pre_topc(X2,X1))
    | ~ v2_compts_1(X1,X2)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_104,negated_conjecture,
    ( ~ v1_compts_1(k1_pre_topc(esk1_0,k1_xboole_0))
    | ~ v2_compts_1(k1_xboole_0,esk1_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102]),c_0_46])])).

cnf(c_0_105,plain,
    ( v1_compts_1(k1_pre_topc(X1,k1_xboole_0))
    | ~ v2_compts_1(k1_xboole_0,X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_103])).

cnf(c_0_106,negated_conjecture,
    ( ~ v2_compts_1(k1_xboole_0,esk1_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_102]),c_0_46])])).

cnf(c_0_107,negated_conjecture,
    ( ~ v2_compts_1(k1_xboole_0,esk1_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_44]),c_0_102]),c_0_46])])).

cnf(c_0_108,negated_conjecture,
    ( ~ v2_compts_1(k1_xboole_0,esk1_0)
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_107,c_0_20])).

cnf(c_0_109,negated_conjecture,
    ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | v2_compts_1(k1_xboole_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_98]),c_0_98])).

cnf(c_0_110,negated_conjecture,
    ( ~ v2_compts_1(k1_xboole_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_13]),c_0_46])])).

cnf(c_0_111,negated_conjecture,
    ( v2_compts_1(k1_xboole_0,esk1_0)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_98]),c_0_98])).

cnf(c_0_112,plain,
    ( v1_compts_1(k1_pre_topc(X1,k1_xboole_0))
    | ~ v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_42])).

cnf(c_0_113,negated_conjecture,
    ( v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(sr,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_114,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(sr,[status(thm)],[c_0_111,c_0_110])).

cnf(c_0_115,negated_conjecture,
    ( v1_compts_1(k1_pre_topc(esk1_0,k1_xboole_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_102]),c_0_46])]),c_0_114])])).

cnf(c_0_116,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_115]),c_0_102]),c_0_46])]),c_0_110])).

cnf(c_0_117,negated_conjecture,
    ( ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_116,c_0_20])).

cnf(c_0_118,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_13]),c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:06:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.56/0.74  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.56/0.74  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.56/0.74  #
% 0.56/0.74  # Preprocessing time       : 0.027 s
% 0.56/0.74  # Presaturation interreduction done
% 0.56/0.74  
% 0.56/0.74  # Proof found!
% 0.56/0.74  # SZS status Theorem
% 0.56/0.74  # SZS output start CNFRefutation
% 0.56/0.74  fof(free_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3, X4]:(g1_pre_topc(X1,X2)=g1_pre_topc(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 0.56/0.74  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.56/0.74  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.56/0.74  fof(dt_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v1_pre_topc(g1_pre_topc(X1,X2))&l1_pre_topc(g1_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 0.56/0.74  fof(t66_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))=>(X2=X3=>g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X2)),u1_pre_topc(k1_pre_topc(X1,X2)))=k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_pre_topc)).
% 0.56/0.74  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.56/0.74  fof(dt_k1_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_pre_topc(k1_pre_topc(X1,X2))&m1_pre_topc(k1_pre_topc(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 0.56/0.74  fof(t33_compts_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v2_compts_1(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))<=>(v2_compts_1(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_compts_1)).
% 0.56/0.74  fof(t12_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((X2=k1_xboole_0=>(v2_compts_1(X2,X1)<=>v1_compts_1(k1_pre_topc(X1,X2))))&(v2_pre_topc(X1)=>(X2=k1_xboole_0|(v2_compts_1(X2,X1)<=>v1_compts_1(k1_pre_topc(X1,X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_compts_1)).
% 0.56/0.74  fof(fc6_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 0.56/0.74  fof(c_0_10, plain, ![X14, X15, X16, X17]:((X14=X16|g1_pre_topc(X14,X15)!=g1_pre_topc(X16,X17)|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))))&(X15=X17|g1_pre_topc(X14,X15)!=g1_pre_topc(X16,X17)|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).
% 0.56/0.74  fof(c_0_11, plain, ![X12]:(~l1_pre_topc(X12)|m1_subset_1(u1_pre_topc(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.56/0.74  cnf(c_0_12, plain, (X1=X2|g1_pre_topc(X3,X1)!=g1_pre_topc(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.56/0.74  cnf(c_0_13, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.56/0.74  fof(c_0_14, plain, ![X5]:(~l1_pre_topc(X5)|(~v1_pre_topc(X5)|X5=g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.56/0.74  cnf(c_0_15, plain, (u1_pre_topc(X1)=X2|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(X3,X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.56/0.74  cnf(c_0_16, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.56/0.74  fof(c_0_17, plain, ![X6, X7]:((v1_pre_topc(g1_pre_topc(X6,X7))|~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X6))))&(l1_pre_topc(g1_pre_topc(X6,X7))|~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(X6))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).
% 0.56/0.74  cnf(c_0_18, plain, (u1_pre_topc(g1_pre_topc(X1,X2))=X2|~v1_pre_topc(g1_pre_topc(X1,X2))|~l1_pre_topc(g1_pre_topc(X1,X2))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16])])).
% 0.56/0.74  cnf(c_0_19, plain, (v1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.56/0.74  cnf(c_0_20, plain, (l1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.56/0.74  cnf(c_0_21, plain, (u1_pre_topc(g1_pre_topc(X1,X2))=X2|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.56/0.74  cnf(c_0_22, plain, (X1=X2|g1_pre_topc(X1,X3)!=g1_pre_topc(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.56/0.74  cnf(c_0_23, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(X2,X1)))))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_21]), c_0_20])).
% 0.56/0.74  fof(c_0_24, plain, ![X18, X19, X20]:(~l1_pre_topc(X18)|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))))|(X19!=X20|g1_pre_topc(u1_struct_0(k1_pre_topc(X18,X19)),u1_pre_topc(k1_pre_topc(X18,X19)))=k1_pre_topc(g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)),X20))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t66_pre_topc])])])).
% 0.56/0.74  fof(c_0_25, plain, ![X10, X11]:(~l1_pre_topc(X10)|(~m1_pre_topc(X11,X10)|l1_pre_topc(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.56/0.74  fof(c_0_26, plain, ![X8, X9]:((v1_pre_topc(k1_pre_topc(X8,X9))|(~l1_pre_topc(X8)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))))&(m1_pre_topc(k1_pre_topc(X8,X9),X8)|(~l1_pre_topc(X8)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).
% 0.56/0.74  cnf(c_0_27, plain, (u1_struct_0(g1_pre_topc(X1,X2))=X3|g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2)!=g1_pre_topc(X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.56/0.74  cnf(c_0_28, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2)=g1_pre_topc(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_21]), c_0_20]), c_0_19])).
% 0.56/0.74  cnf(c_0_29, plain, (u1_struct_0(X1)=X2|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(X2,X3)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_22, c_0_13])).
% 0.56/0.74  cnf(c_0_30, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X2)),u1_pre_topc(k1_pre_topc(X1,X2)))=k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))|X2!=X3), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.56/0.74  cnf(c_0_31, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.56/0.74  cnf(c_0_32, plain, (m1_pre_topc(k1_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.56/0.74  cnf(c_0_33, plain, (u1_struct_0(g1_pre_topc(X1,X2))=X3|g1_pre_topc(X1,X2)!=g1_pre_topc(X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.56/0.74  cnf(c_0_34, plain, (u1_struct_0(g1_pre_topc(X1,X2))=X1|~v1_pre_topc(g1_pre_topc(X1,X2))|~l1_pre_topc(g1_pre_topc(X1,X2))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_16])])).
% 0.56/0.74  fof(c_0_35, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v2_compts_1(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))<=>(v2_compts_1(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))))), inference(assume_negation,[status(cth)],[t33_compts_1])).
% 0.56/0.74  cnf(c_0_36, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X2)),u1_pre_topc(k1_pre_topc(X1,X2)))=k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(er,[status(thm)],[c_0_30])).
% 0.56/0.74  cnf(c_0_37, plain, (l1_pre_topc(k1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.56/0.74  cnf(c_0_38, plain, (v1_pre_topc(k1_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.56/0.74  cnf(c_0_39, plain, (u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=X2|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(X2,X3)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_33, c_0_13])).
% 0.56/0.74  cnf(c_0_40, plain, (u1_struct_0(g1_pre_topc(X1,X2))=X1|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_19]), c_0_20])).
% 0.56/0.74  fof(c_0_41, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_compts_1(esk2_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|(~v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))))&(((v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|v2_compts_1(esk2_0,esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|v2_compts_1(esk2_0,esk1_0)))&((v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_35])])])])])).
% 0.56/0.74  cnf(c_0_42, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)=k1_pre_topc(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_36]), c_0_37]), c_0_38])).
% 0.56/0.74  cnf(c_0_43, plain, (u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=u1_struct_0(k1_pre_topc(X2,X3))|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=k1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_39, c_0_36])).
% 0.56/0.74  cnf(c_0_44, plain, (u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_40, c_0_13])).
% 0.56/0.74  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.56/0.74  cnf(c_0_46, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.56/0.74  cnf(c_0_47, plain, (k1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2),X3)=k1_pre_topc(g1_pre_topc(X1,X2),X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2))))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_21]), c_0_20])).
% 0.56/0.74  cnf(c_0_48, plain, (u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=u1_struct_0(k1_pre_topc(X2,X3))|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=k1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.56/0.74  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_44]), c_0_46])])).
% 0.56/0.74  cnf(c_0_50, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(X1,X2),X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2))))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2))), inference(spm,[status(thm)],[c_0_38, c_0_47])).
% 0.56/0.74  cnf(c_0_51, plain, (u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2))=u1_struct_0(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_40, c_0_23])).
% 0.56/0.74  cnf(c_0_52, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=u1_struct_0(k1_pre_topc(esk1_0,esk2_0))|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_46])])).
% 0.56/0.74  cnf(c_0_53, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(X1,X2),X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2))))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.56/0.74  cnf(c_0_54, plain, (l1_pre_topc(k1_pre_topc(g1_pre_topc(X1,X2),X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2))))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2))), inference(spm,[status(thm)],[c_0_37, c_0_47])).
% 0.56/0.74  cnf(c_0_55, negated_conjecture, (u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))=u1_struct_0(k1_pre_topc(esk1_0,esk2_0))|~v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))|~l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_16])])).
% 0.56/0.74  cnf(c_0_56, plain, (v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_44]), c_0_20]), c_0_13])).
% 0.56/0.74  cnf(c_0_57, plain, (l1_pre_topc(k1_pre_topc(g1_pre_topc(X1,X2),X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2))))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2))), inference(spm,[status(thm)],[c_0_54, c_0_51])).
% 0.56/0.74  cnf(c_0_58, negated_conjecture, (u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))=u1_struct_0(k1_pre_topc(esk1_0,esk2_0))|~l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_49]), c_0_46])])).
% 0.56/0.74  cnf(c_0_59, plain, (l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_44]), c_0_20]), c_0_13])).
% 0.56/0.74  fof(c_0_60, plain, ![X21, X22]:(((~v2_compts_1(X22,X21)|v1_compts_1(k1_pre_topc(X21,X22))|X22!=k1_xboole_0|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~l1_pre_topc(X21))&(~v1_compts_1(k1_pre_topc(X21,X22))|v2_compts_1(X22,X21)|X22!=k1_xboole_0|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~l1_pre_topc(X21)))&((~v2_compts_1(X22,X21)|v1_compts_1(k1_pre_topc(X21,X22))|X22=k1_xboole_0|~v2_pre_topc(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~l1_pre_topc(X21))&(~v1_compts_1(k1_pre_topc(X21,X22))|v2_compts_1(X22,X21)|X22=k1_xboole_0|~v2_pre_topc(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~l1_pre_topc(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_compts_1])])])])).
% 0.56/0.74  cnf(c_0_61, negated_conjecture, (u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))=u1_struct_0(k1_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_49]), c_0_46])])).
% 0.56/0.74  cnf(c_0_62, plain, (u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))=u1_pre_topc(k1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))|~l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_18, c_0_36])).
% 0.56/0.74  cnf(c_0_63, plain, (v1_compts_1(k1_pre_topc(X2,X1))|X1=k1_xboole_0|~v2_compts_1(X1,X2)|~v2_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.56/0.74  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|v2_compts_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.56/0.74  cnf(c_0_65, negated_conjecture, (v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|v2_compts_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.56/0.74  fof(c_0_66, plain, ![X13]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))|(~v2_pre_topc(X13)|~l1_pre_topc(X13)))&(v2_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))|(~v2_pre_topc(X13)|~l1_pre_topc(X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).
% 0.56/0.74  cnf(c_0_67, negated_conjecture, (m1_subset_1(u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)))))|~l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))), inference(spm,[status(thm)],[c_0_13, c_0_61])).
% 0.56/0.74  cnf(c_0_68, plain, (u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))=u1_pre_topc(k1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_38]), c_0_37])).
% 0.56/0.74  cnf(c_0_69, negated_conjecture, (esk2_0=k1_xboole_0|v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))|v2_compts_1(esk2_0,esk1_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 0.56/0.74  cnf(c_0_70, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.56/0.74  cnf(c_0_71, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.56/0.74  cnf(c_0_72, plain, (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_16, c_0_44])).
% 0.56/0.74  cnf(c_0_73, plain, (u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))=u1_pre_topc(k1_pre_topc(X1,X2))|~m1_subset_1(u1_pre_topc(k1_pre_topc(X1,X2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_21, c_0_36])).
% 0.56/0.74  cnf(c_0_74, negated_conjecture, (m1_subset_1(u1_pre_topc(k1_pre_topc(esk1_0,esk2_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)))))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_49]), c_0_46])]), c_0_37])).
% 0.56/0.74  cnf(c_0_75, negated_conjecture, (esk2_0=k1_xboole_0|v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))|v2_compts_1(esk2_0,esk1_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_46])])).
% 0.56/0.74  cnf(c_0_76, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X2)),u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)))=k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_36]), c_0_37]), c_0_59]), c_0_56])).
% 0.56/0.74  cnf(c_0_77, negated_conjecture, (u1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))=u1_pre_topc(k1_pre_topc(esk1_0,esk2_0))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_49]), c_0_46])])).
% 0.56/0.74  cnf(c_0_78, negated_conjecture, (esk2_0=k1_xboole_0|v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))|v2_compts_1(esk2_0,esk1_0)|~m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_75, c_0_20])).
% 0.56/0.74  cnf(c_0_79, plain, (v2_compts_1(X2,X1)|X2=k1_xboole_0|~v1_compts_1(k1_pre_topc(X1,X2))|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.56/0.74  cnf(c_0_80, negated_conjecture, (g1_pre_topc(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)),u1_pre_topc(k1_pre_topc(esk1_0,esk2_0)))=k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_49]), c_0_46])])).
% 0.56/0.74  cnf(c_0_81, plain, (g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X2)),u1_pre_topc(k1_pre_topc(X1,X2)))=k1_pre_topc(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_76, c_0_42])).
% 0.56/0.74  cnf(c_0_82, negated_conjecture, (esk2_0=k1_xboole_0|v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))|v2_compts_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_13]), c_0_46])])).
% 0.56/0.74  cnf(c_0_83, negated_conjecture, (esk2_0=k1_xboole_0|v1_compts_1(k1_pre_topc(esk1_0,esk2_0))|~v2_compts_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_49]), c_0_71]), c_0_46])])).
% 0.56/0.74  cnf(c_0_84, plain, (X1=k1_xboole_0|v2_compts_1(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~v1_compts_1(k1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1))|~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_79, c_0_44])).
% 0.56/0.74  cnf(c_0_85, negated_conjecture, (k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)=k1_pre_topc(esk1_0,esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_49]), c_0_46])])).
% 0.56/0.74  cnf(c_0_86, negated_conjecture, (esk2_0=k1_xboole_0|v1_compts_1(k1_pre_topc(esk1_0,esk2_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_42]), c_0_49]), c_0_46])]), c_0_64]), c_0_83])).
% 0.56/0.74  cnf(c_0_87, negated_conjecture, (esk2_0=k1_xboole_0|v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_49]), c_0_46])]), c_0_86])).
% 0.56/0.74  cnf(c_0_88, negated_conjecture, (esk2_0=k1_xboole_0|v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_70]), c_0_71]), c_0_46])])).
% 0.56/0.74  cnf(c_0_89, negated_conjecture, (esk2_0=k1_xboole_0|v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|~m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_88, c_0_20])).
% 0.56/0.74  cnf(c_0_90, negated_conjecture, (~v2_compts_1(esk2_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))|~v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.56/0.74  cnf(c_0_91, negated_conjecture, (esk2_0=k1_xboole_0|v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_13]), c_0_46])])).
% 0.56/0.74  cnf(c_0_92, negated_conjecture, (esk2_0=k1_xboole_0|v2_compts_1(esk2_0,esk1_0)|~v1_compts_1(k1_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_49]), c_0_71]), c_0_46])])).
% 0.56/0.74  cnf(c_0_93, negated_conjecture, (~v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v2_compts_1(esk2_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_49])])).
% 0.56/0.74  cnf(c_0_94, negated_conjecture, (esk2_0=k1_xboole_0|v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_44]), c_0_49]), c_0_46])])).
% 0.56/0.74  cnf(c_0_95, negated_conjecture, (esk2_0=k1_xboole_0|v2_compts_1(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_92, c_0_86])).
% 0.56/0.74  cnf(c_0_96, negated_conjecture, (esk2_0=k1_xboole_0|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95])).
% 0.56/0.74  cnf(c_0_97, plain, (v2_compts_1(X2,X1)|~v1_compts_1(k1_pre_topc(X1,X2))|X2!=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.56/0.74  cnf(c_0_98, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_44]), c_0_49]), c_0_46])])).
% 0.56/0.74  cnf(c_0_99, plain, (v2_compts_1(k1_xboole_0,X1)|~v1_compts_1(k1_pre_topc(X1,k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(er,[status(thm)],[c_0_97])).
% 0.56/0.74  cnf(c_0_100, negated_conjecture, (~v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v2_compts_1(k1_xboole_0,esk1_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_98]), c_0_98]), c_0_98])).
% 0.56/0.74  cnf(c_0_101, plain, (v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v1_compts_1(k1_pre_topc(X1,k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_99, c_0_42])).
% 0.56/0.74  cnf(c_0_102, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[c_0_49, c_0_98])).
% 0.56/0.74  cnf(c_0_103, plain, (v1_compts_1(k1_pre_topc(X2,X1))|~v2_compts_1(X1,X2)|X1!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.56/0.74  cnf(c_0_104, negated_conjecture, (~v1_compts_1(k1_pre_topc(esk1_0,k1_xboole_0))|~v2_compts_1(k1_xboole_0,esk1_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_102]), c_0_46])])).
% 0.56/0.74  cnf(c_0_105, plain, (v1_compts_1(k1_pre_topc(X1,k1_xboole_0))|~v2_compts_1(k1_xboole_0,X1)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(er,[status(thm)],[c_0_103])).
% 0.56/0.74  cnf(c_0_106, negated_conjecture, (~v2_compts_1(k1_xboole_0,esk1_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_102]), c_0_46])])).
% 0.56/0.74  cnf(c_0_107, negated_conjecture, (~v2_compts_1(k1_xboole_0,esk1_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_44]), c_0_102]), c_0_46])])).
% 0.56/0.74  cnf(c_0_108, negated_conjecture, (~v2_compts_1(k1_xboole_0,esk1_0)|~m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_107, c_0_20])).
% 0.56/0.74  cnf(c_0_109, negated_conjecture, (v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|v2_compts_1(k1_xboole_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_98]), c_0_98])).
% 0.56/0.74  cnf(c_0_110, negated_conjecture, (~v2_compts_1(k1_xboole_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_13]), c_0_46])])).
% 0.56/0.74  cnf(c_0_111, negated_conjecture, (v2_compts_1(k1_xboole_0,esk1_0)|m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_98]), c_0_98])).
% 0.56/0.74  cnf(c_0_112, plain, (v1_compts_1(k1_pre_topc(X1,k1_xboole_0))|~v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_105, c_0_42])).
% 0.56/0.74  cnf(c_0_113, negated_conjecture, (v2_compts_1(k1_xboole_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(sr,[status(thm)],[c_0_109, c_0_110])).
% 0.56/0.74  cnf(c_0_114, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))), inference(sr,[status(thm)],[c_0_111, c_0_110])).
% 0.56/0.74  cnf(c_0_115, negated_conjecture, (v1_compts_1(k1_pre_topc(esk1_0,k1_xboole_0))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_102]), c_0_46])]), c_0_114])])).
% 0.56/0.74  cnf(c_0_116, negated_conjecture, (~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_115]), c_0_102]), c_0_46])]), c_0_110])).
% 0.56/0.74  cnf(c_0_117, negated_conjecture, (~m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_116, c_0_20])).
% 0.56/0.74  cnf(c_0_118, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_13]), c_0_46])]), ['proof']).
% 0.56/0.74  # SZS output end CNFRefutation
% 0.56/0.74  # Proof object total steps             : 119
% 0.56/0.74  # Proof object clause steps            : 98
% 0.56/0.74  # Proof object formula steps           : 21
% 0.56/0.74  # Proof object conjectures             : 50
% 0.56/0.74  # Proof object clause conjectures      : 47
% 0.56/0.74  # Proof object formula conjectures     : 3
% 0.56/0.74  # Proof object initial clauses used    : 21
% 0.56/0.74  # Proof object initial formulas used   : 10
% 0.56/0.74  # Proof object generating inferences   : 67
% 0.56/0.74  # Proof object simplifying inferences  : 112
% 0.56/0.74  # Training examples: 0 positive, 0 negative
% 0.56/0.74  # Parsed axioms                        : 10
% 0.56/0.74  # Removed by relevancy pruning/SinE    : 0
% 0.56/0.74  # Initial clauses                      : 24
% 0.56/0.74  # Removed in clause preprocessing      : 0
% 0.56/0.74  # Initial clauses in saturation        : 24
% 0.56/0.74  # Processed clauses                    : 1805
% 0.56/0.74  # ...of these trivial                  : 47
% 0.56/0.74  # ...subsumed                          : 1271
% 0.56/0.74  # ...remaining for further processing  : 487
% 0.56/0.74  # Other redundant clauses eliminated   : 89
% 0.56/0.74  # Clauses deleted for lack of memory   : 0
% 0.56/0.74  # Backward-subsumed                    : 123
% 0.56/0.74  # Backward-rewritten                   : 104
% 0.56/0.74  # Generated clauses                    : 14425
% 0.56/0.74  # ...of the previous two non-trivial   : 14088
% 0.56/0.74  # Contextual simplify-reflections      : 119
% 0.56/0.74  # Paramodulations                      : 14283
% 0.56/0.74  # Factorizations                       : 0
% 0.56/0.74  # Equation resolutions                 : 137
% 0.56/0.74  # Propositional unsat checks           : 0
% 0.56/0.74  #    Propositional check models        : 0
% 0.56/0.74  #    Propositional check unsatisfiable : 0
% 0.56/0.74  #    Propositional clauses             : 0
% 0.56/0.74  #    Propositional clauses after purity: 0
% 0.56/0.74  #    Propositional unsat core size     : 0
% 0.56/0.74  #    Propositional preprocessing time  : 0.000
% 0.56/0.74  #    Propositional encoding time       : 0.000
% 0.56/0.74  #    Propositional solver time         : 0.000
% 0.56/0.74  #    Success case prop preproc time    : 0.000
% 0.56/0.74  #    Success case prop encoding time   : 0.000
% 0.56/0.74  #    Success case prop solver time     : 0.000
% 0.56/0.74  # Current number of processed clauses  : 228
% 0.56/0.74  #    Positive orientable unit clauses  : 11
% 0.56/0.74  #    Positive unorientable unit clauses: 0
% 0.56/0.74  #    Negative unit clauses             : 5
% 0.56/0.74  #    Non-unit-clauses                  : 212
% 0.56/0.74  # Current number of unprocessed clauses: 12060
% 0.56/0.74  # ...number of literals in the above   : 80879
% 0.56/0.74  # Current number of archived formulas  : 0
% 0.56/0.74  # Current number of archived clauses   : 256
% 0.56/0.74  # Clause-clause subsumption calls (NU) : 36164
% 0.56/0.74  # Rec. Clause-clause subsumption calls : 9784
% 0.56/0.74  # Non-unit clause-clause subsumptions  : 1396
% 0.56/0.74  # Unit Clause-clause subsumption calls : 25
% 0.56/0.74  # Rewrite failures with RHS unbound    : 0
% 0.56/0.74  # BW rewrite match attempts            : 13
% 0.56/0.74  # BW rewrite match successes           : 6
% 0.56/0.74  # Condensation attempts                : 0
% 0.56/0.74  # Condensation successes               : 0
% 0.56/0.74  # Termbank termtop insertions          : 809081
% 0.56/0.74  
% 0.56/0.74  # -------------------------------------------------
% 0.56/0.74  # User time                : 0.389 s
% 0.56/0.74  # System time              : 0.012 s
% 0.56/0.74  # Total time               : 0.400 s
% 0.56/0.74  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
