%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1130+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:47 EST 2020

% Result     : Theorem 0.91s
% Output     : CNFRefutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 593 expanded)
%              Number of clauses        :   63 ( 271 expanded)
%              Number of leaves         :   12 ( 154 expanded)
%              Depth                    :   17
%              Number of atoms          :  293 (1892 expanded)
%              Number of equality atoms :   41 ( 321 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d6_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(t61_pre_topc,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v4_pre_topc(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( v4_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_pre_topc)).

fof(dt_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(c_0_12,plain,(
    ! [X19,X20,X21,X22] :
      ( ( X19 = X21
        | g1_pre_topc(X19,X20) != g1_pre_topc(X21,X22)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))) )
      & ( X20 = X22
        | g1_pre_topc(X19,X20) != g1_pre_topc(X21,X22)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_13,plain,(
    ! [X18] :
      ( ~ l1_pre_topc(X18)
      | m1_subset_1(u1_pre_topc(X18),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_14,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | ~ v1_pre_topc(X5)
      | X5 = g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

fof(c_0_17,plain,(
    ! [X6] :
      ( ~ l1_struct_0(X6)
      | k2_struct_0(X6) = u1_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_18,plain,(
    ! [X17] :
      ( ~ l1_pre_topc(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_19,plain,
    ( u1_pre_topc(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X9,X10] :
      ( ( ~ v4_pre_topc(X10,X9)
        | v3_pre_topc(k7_subset_1(u1_struct_0(X9),k2_struct_0(X9),X10),X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) )
      & ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X9),k2_struct_0(X9),X10),X9)
        | v4_pre_topc(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_pre_topc])])])])).

cnf(c_0_22,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X13] :
      ( ~ l1_struct_0(X13)
      | m1_subset_1(k2_struct_0(X13),k1_zfmisc_1(u1_struct_0(X13))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_25,plain,
    ( u1_pre_topc(X1) = X2
    | X1 != g1_pre_topc(X3,X2)
    | ~ v1_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_26,plain,(
    ! [X11,X12] :
      ( ( v1_pre_topc(g1_pre_topc(X11,X12))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11))) )
      & ( l1_pre_topc(g1_pre_topc(X11,X12))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

cnf(c_0_27,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_30,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | k7_subset_1(X23,X24,X25) = k4_xboole_0(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_31,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_32,plain,(
    ! [X7,X8] :
      ( ( ~ v3_pre_topc(X8,X7)
        | r2_hidden(X8,u1_pre_topc(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) )
      & ( ~ r2_hidden(X8,u1_pre_topc(X7))
        | v3_pre_topc(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_33,plain,
    ( u1_pre_topc(g1_pre_topc(X1,X2)) = X2
    | ~ v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ l1_pre_topc(g1_pre_topc(X1,X2)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( u1_struct_0(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_15])).

cnf(c_0_37,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X2),u1_struct_0(X2),X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_29]),c_0_23])).

cnf(c_0_40,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( u1_pre_topc(g1_pre_topc(X1,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_42,plain,
    ( u1_struct_0(X1) = X2
    | X1 != g1_pre_topc(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_20])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),X1),X2)
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_45,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v4_pre_topc(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          <=> ( v4_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t61_pre_topc])).

cnf(c_0_46,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v3_pre_topc(k4_xboole_0(u1_struct_0(X2),X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_47,plain,
    ( v3_pre_topc(X1,g1_pre_topc(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X2,X3))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_35])).

cnf(c_0_48,plain,
    ( u1_struct_0(g1_pre_topc(X1,X2)) = X1
    | ~ v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ l1_pre_topc(g1_pre_topc(X1,X2)) ),
    inference(er,[status(thm)],[c_0_42])).

fof(c_0_49,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | m1_subset_1(k7_subset_1(X14,X15,X16),k1_zfmisc_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | ~ v3_pre_topc(X1,g1_pre_topc(X3,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X3,X2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_41]),c_0_35])).

cnf(c_0_51,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X1),u1_struct_0(X1),X2),X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_29])).

fof(c_0_52,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ( ~ v4_pre_topc(esk2_0,esk1_0)
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      | ~ v4_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) )
    & ( v4_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
      | v4_pre_topc(esk2_0,esk1_0) )
    & ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
      | v4_pre_topc(esk2_0,esk1_0) )
    & ( v4_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
      | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) )
    & ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
      | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_45])])])])).

cnf(c_0_53,plain,
    ( v4_pre_topc(X1,g1_pre_topc(X2,X3))
    | ~ r2_hidden(k4_xboole_0(u1_struct_0(g1_pre_topc(X2,X3)),X1),X3)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(g1_pre_topc(X2,X3)),X1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(X2,X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X2,X3))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_35])).

cnf(c_0_54,plain,
    ( u1_struct_0(g1_pre_topc(X1,X2)) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_34]),c_0_35])).

cnf(c_0_55,plain,
    ( m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( r2_hidden(k7_subset_1(u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(g1_pre_topc(X1,X2)),X3),X2)
    | ~ v4_pre_topc(X3,g1_pre_topc(X1,X2))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(g1_pre_topc(X1,X2)),X3),k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_35])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,plain,
    ( v4_pre_topc(X1,g1_pre_topc(X2,X3))
    | ~ r2_hidden(k4_xboole_0(X2,X1),X3)
    | ~ m1_subset_1(k4_xboole_0(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_38])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_54]),c_0_35])).

cnf(c_0_61,plain,
    ( r2_hidden(k7_subset_1(X1,X1,X2),X3)
    | ~ v4_pre_topc(X2,g1_pre_topc(X1,X3))
    | ~ m1_subset_1(k7_subset_1(X1,X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,plain,
    ( v4_pre_topc(X1,g1_pre_topc(X2,X3))
    | ~ r2_hidden(k4_xboole_0(X2,X1),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_65,plain,
    ( v3_pre_topc(k4_xboole_0(k2_struct_0(X1),X2),X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_38])).

cnf(c_0_66,plain,
    ( r2_hidden(k7_subset_1(X1,X1,X2),X3)
    | ~ v4_pre_topc(X2,g1_pre_topc(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_55]),c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( ~ v4_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v4_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_15]),c_0_63])])).

cnf(c_0_69,plain,
    ( v4_pre_topc(X1,g1_pre_topc(X2,u1_pre_topc(X3)))
    | ~ v3_pre_topc(k4_xboole_0(X2,X1),X3)
    | ~ m1_subset_1(k4_xboole_0(X2,X1),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(u1_pre_topc(X3),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_64,c_0_43])).

cnf(c_0_70,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(X1),X2),X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_29]),c_0_39])).

cnf(c_0_71,plain,
    ( u1_struct_0(g1_pre_topc(X1,X2)) = X3
    | g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2) != g1_pre_topc(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_41]),c_0_35])).

cnf(c_0_72,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),X2) = g1_pre_topc(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_41]),c_0_35]),c_0_34])).

cnf(c_0_73,plain,
    ( r2_hidden(k4_xboole_0(X1,X2),X3)
    | ~ v4_pre_topc(X2,g1_pre_topc(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_38]),c_0_60])).

cnf(c_0_74,negated_conjecture,
    ( ~ v4_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v4_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68])])).

cnf(c_0_75,plain,
    ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(X2),X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_15])).

cnf(c_0_76,plain,
    ( u1_struct_0(g1_pre_topc(X1,X2)) = X3
    | g1_pre_topc(X1,X2) != g1_pre_topc(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,plain,
    ( v3_pre_topc(k4_xboole_0(X1,X2),X3)
    | ~ v4_pre_topc(X2,g1_pre_topc(X1,u1_pre_topc(X3)))
    | ~ m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(u1_pre_topc(X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( ~ v4_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_68]),c_0_63])])).

cnf(c_0_79,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_15])).

cnf(c_0_80,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(X2),X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_77]),c_0_15])).

cnf(c_0_81,negated_conjecture,
    ( v4_pre_topc(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | v4_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_82,negated_conjecture,
    ( ~ v4_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_59])).

cnf(c_0_83,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_68]),c_0_63])])).

cnf(c_0_85,negated_conjecture,
    ( ~ v4_pre_topc(esk2_0,esk1_0)
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_68]),c_0_63])])).

cnf(c_0_86,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_59]),c_0_85])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_39]),c_0_63])]),
    [proof]).

%------------------------------------------------------------------------------
