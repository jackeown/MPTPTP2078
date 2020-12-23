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
% DateTime   : Thu Dec  3 11:18:24 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 221 expanded)
%              Number of clauses        :   31 (  80 expanded)
%              Number of leaves         :    6 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  281 (1630 expanded)
%              Number of equality atoms :   44 ( 235 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t106_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t116_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( ( v1_tsep_1(X2,X1)
              & m1_pre_topc(X2,X1) )
          <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k8_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(d11_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X3 = k8_tmap_1(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X4 = u1_struct_0(X2)
                     => X3 = k6_tmap_1(X1,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).

fof(dt_k8_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2))
        & l1_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(c_0_6,plain,(
    ! [X12,X13] :
      ( ( ~ v3_pre_topc(X13,X12)
        | g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)) = k6_tmap_1(X12,X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)) != k6_tmap_1(X12,X13)
        | v3_pre_topc(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t106_tmap_1])])])])])).

fof(c_0_7,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(X18,X17)
      | m1_subset_1(u1_struct_0(X18),k1_zfmisc_1(u1_struct_0(X17))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ( ( v1_tsep_1(X2,X1)
                & m1_pre_topc(X2,X1) )
            <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k8_tmap_1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t116_tmap_1])).

fof(c_0_9,plain,(
    ! [X14,X15,X16] :
      ( ( ~ v1_tsep_1(X15,X14)
        | ~ m1_pre_topc(X15,X14)
        | v3_pre_topc(X16,X14)
        | X16 != u1_struct_0(X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ m1_pre_topc(X15,X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( v1_tsep_1(X15,X14)
        | ~ v3_pre_topc(X16,X14)
        | X16 != u1_struct_0(X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ m1_pre_topc(X15,X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_pre_topc(X15,X14)
        | ~ v3_pre_topc(X16,X14)
        | X16 != u1_struct_0(X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ m1_pre_topc(X15,X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).

cnf(c_0_10,plain,
    ( v3_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k6_tmap_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & ( ~ v1_tsep_1(esk3_0,esk2_0)
      | ~ m1_pre_topc(esk3_0,esk2_0)
      | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != k8_tmap_1(esk2_0,esk3_0) )
    & ( v1_tsep_1(esk3_0,esk2_0)
      | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k8_tmap_1(esk2_0,esk3_0) )
    & ( m1_pre_topc(esk3_0,esk2_0)
      | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k8_tmap_1(esk2_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).

cnf(c_0_13,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | v2_struct_0(X2)
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k6_tmap_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v1_tsep_1(esk3_0,esk2_0)
    | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = k8_tmap_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X5,X6,X7,X8] :
      ( ( X7 != k8_tmap_1(X5,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X5)))
        | X8 != u1_struct_0(X6)
        | X7 = k6_tmap_1(X5,X8)
        | ~ v1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( m1_subset_1(esk1_3(X5,X6,X7),k1_zfmisc_1(u1_struct_0(X5)))
        | X7 = k8_tmap_1(X5,X6)
        | ~ v1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( esk1_3(X5,X6,X7) = u1_struct_0(X6)
        | X7 = k8_tmap_1(X5,X6)
        | ~ v1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) )
      & ( X7 != k6_tmap_1(X5,esk1_3(X5,X6,X7))
        | X7 = k8_tmap_1(X5,X6)
        | ~ v1_pre_topc(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_20,plain,(
    ! [X10,X11] :
      ( ( v1_pre_topc(k8_tmap_1(X10,X11))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10)
        | ~ m1_pre_topc(X11,X10) )
      & ( v2_pre_topc(k8_tmap_1(X10,X11))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10)
        | ~ m1_pre_topc(X11,X10) )
      & ( l1_pre_topc(k8_tmap_1(X10,X11))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10)
        | ~ m1_pre_topc(X11,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

cnf(c_0_21,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( v1_tsep_1(esk3_0,esk2_0)
    | v3_pre_topc(u1_struct_0(X1),esk2_0)
    | k6_tmap_1(esk2_0,u1_struct_0(X1)) != k8_tmap_1(esk2_0,esk3_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_23,plain,
    ( X1 = k6_tmap_1(X2,X4)
    | v2_struct_0(X2)
    | X1 != k8_tmap_1(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != u1_struct_0(X3)
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( v1_tsep_1(esk3_0,esk2_0)
    | v1_tsep_1(X1,esk2_0)
    | k6_tmap_1(esk2_0,u1_struct_0(X1)) != k8_tmap_1(esk2_0,esk3_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_16]),c_0_17])])).

cnf(c_0_28,plain,
    ( k6_tmap_1(X1,u1_struct_0(X2)) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])]),c_0_24]),c_0_25]),c_0_26]),c_0_11])).

cnf(c_0_29,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_tsep_1(esk3_0,esk2_0)
    | ~ m1_pre_topc(esk3_0,esk2_0)
    | g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != k8_tmap_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( v1_tsep_1(esk3_0,esk2_0)
    | v1_tsep_1(X1,esk2_0)
    | k8_tmap_1(esk2_0,X1) != k8_tmap_1(esk2_0,esk3_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_33,plain,
    ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k6_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_34,plain,
    ( v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != k8_tmap_1(esk2_0,esk3_0)
    | ~ v1_tsep_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])])).

cnf(c_0_36,negated_conjecture,
    ( v1_tsep_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

cnf(c_0_37,plain,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ v3_pre_topc(u1_struct_0(X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_11])).

cnf(c_0_38,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_11])).

cnf(c_0_39,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) != k8_tmap_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])])).

cnf(c_0_40,plain,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( k6_tmap_1(esk2_0,u1_struct_0(X1)) != k8_tmap_1(esk2_0,esk3_0)
    | ~ v1_tsep_1(X1,esk2_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_42,negated_conjecture,
    ( k8_tmap_1(esk2_0,X1) != k8_tmap_1(esk2_0,esk3_0)
    | ~ v1_tsep_1(X1,esk2_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_28]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_36]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.31  % Computer   : n020.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 12:41:07 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.11/0.35  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.11/0.35  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.11/0.35  #
% 0.11/0.35  # Preprocessing time       : 0.028 s
% 0.11/0.35  
% 0.11/0.35  # Proof found!
% 0.11/0.35  # SZS status Theorem
% 0.11/0.35  # SZS output start CNFRefutation
% 0.11/0.35  fof(t106_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 0.11/0.35  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.11/0.35  fof(t116_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_tmap_1)).
% 0.11/0.35  fof(t16_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 0.11/0.35  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_tmap_1)).
% 0.11/0.35  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.11/0.35  fof(c_0_6, plain, ![X12, X13]:((~v3_pre_topc(X13,X12)|g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12))=k6_tmap_1(X12,X13)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12))!=k6_tmap_1(X12,X13)|v3_pre_topc(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t106_tmap_1])])])])])).
% 0.11/0.35  fof(c_0_7, plain, ![X17, X18]:(~l1_pre_topc(X17)|(~m1_pre_topc(X18,X17)|m1_subset_1(u1_struct_0(X18),k1_zfmisc_1(u1_struct_0(X17))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.11/0.35  fof(c_0_8, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k8_tmap_1(X1,X2))))), inference(assume_negation,[status(cth)],[t116_tmap_1])).
% 0.11/0.35  fof(c_0_9, plain, ![X14, X15, X16]:((~v1_tsep_1(X15,X14)|~m1_pre_topc(X15,X14)|v3_pre_topc(X16,X14)|X16!=u1_struct_0(X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|~m1_pre_topc(X15,X14)|(~v2_pre_topc(X14)|~l1_pre_topc(X14)))&((v1_tsep_1(X15,X14)|~v3_pre_topc(X16,X14)|X16!=u1_struct_0(X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|~m1_pre_topc(X15,X14)|(~v2_pre_topc(X14)|~l1_pre_topc(X14)))&(m1_pre_topc(X15,X14)|~v3_pre_topc(X16,X14)|X16!=u1_struct_0(X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|~m1_pre_topc(X15,X14)|(~v2_pre_topc(X14)|~l1_pre_topc(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).
% 0.11/0.35  cnf(c_0_10, plain, (v3_pre_topc(X2,X1)|v2_struct_0(X1)|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=k6_tmap_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.35  cnf(c_0_11, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.11/0.35  fof(c_0_12, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&((~v1_tsep_1(esk3_0,esk2_0)|~m1_pre_topc(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=k8_tmap_1(esk2_0,esk3_0))&((v1_tsep_1(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k8_tmap_1(esk2_0,esk3_0))&(m1_pre_topc(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k8_tmap_1(esk2_0,esk3_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).
% 0.11/0.35  cnf(c_0_13, plain, (v1_tsep_1(X1,X2)|~v3_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.11/0.35  cnf(c_0_14, plain, (v3_pre_topc(u1_struct_0(X1),X2)|v2_struct_0(X2)|g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))!=k6_tmap_1(X2,u1_struct_0(X1))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.11/0.35  cnf(c_0_15, negated_conjecture, (v1_tsep_1(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=k8_tmap_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.35  cnf(c_0_16, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.35  cnf(c_0_17, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.35  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.35  fof(c_0_19, plain, ![X5, X6, X7, X8]:((X7!=k8_tmap_1(X5,X6)|(~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X5)))|(X8!=u1_struct_0(X6)|X7=k6_tmap_1(X5,X8)))|(~v1_pre_topc(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7))|~m1_pre_topc(X6,X5)|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5)))&((m1_subset_1(esk1_3(X5,X6,X7),k1_zfmisc_1(u1_struct_0(X5)))|X7=k8_tmap_1(X5,X6)|(~v1_pre_topc(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7))|~m1_pre_topc(X6,X5)|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5)))&((esk1_3(X5,X6,X7)=u1_struct_0(X6)|X7=k8_tmap_1(X5,X6)|(~v1_pre_topc(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7))|~m1_pre_topc(X6,X5)|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5)))&(X7!=k6_tmap_1(X5,esk1_3(X5,X6,X7))|X7=k8_tmap_1(X5,X6)|(~v1_pre_topc(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7))|~m1_pre_topc(X6,X5)|(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 0.11/0.35  fof(c_0_20, plain, ![X10, X11]:(((v1_pre_topc(k8_tmap_1(X10,X11))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)|~m1_pre_topc(X11,X10)))&(v2_pre_topc(k8_tmap_1(X10,X11))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)|~m1_pre_topc(X11,X10))))&(l1_pre_topc(k8_tmap_1(X10,X11))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)|~m1_pre_topc(X11,X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.11/0.35  cnf(c_0_21, plain, (v1_tsep_1(X1,X2)|~v3_pre_topc(u1_struct_0(X1),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]), c_0_11])).
% 0.11/0.35  cnf(c_0_22, negated_conjecture, (v1_tsep_1(esk3_0,esk2_0)|v3_pre_topc(u1_struct_0(X1),esk2_0)|k6_tmap_1(esk2_0,u1_struct_0(X1))!=k8_tmap_1(esk2_0,esk3_0)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.11/0.35  cnf(c_0_23, plain, (X1=k6_tmap_1(X2,X4)|v2_struct_0(X2)|X1!=k8_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.11/0.35  cnf(c_0_24, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.11/0.35  cnf(c_0_25, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.11/0.35  cnf(c_0_26, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.11/0.35  cnf(c_0_27, negated_conjecture, (v1_tsep_1(esk3_0,esk2_0)|v1_tsep_1(X1,esk2_0)|k6_tmap_1(esk2_0,u1_struct_0(X1))!=k8_tmap_1(esk2_0,esk3_0)|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_16]), c_0_17])])).
% 0.11/0.35  cnf(c_0_28, plain, (k6_tmap_1(X1,u1_struct_0(X2))=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])]), c_0_24]), c_0_25]), c_0_26]), c_0_11])).
% 0.11/0.35  cnf(c_0_29, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.11/0.35  cnf(c_0_30, negated_conjecture, (~v1_tsep_1(esk3_0,esk2_0)|~m1_pre_topc(esk3_0,esk2_0)|g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=k8_tmap_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.35  cnf(c_0_31, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.35  cnf(c_0_32, negated_conjecture, (v1_tsep_1(esk3_0,esk2_0)|v1_tsep_1(X1,esk2_0)|k8_tmap_1(esk2_0,X1)!=k8_tmap_1(esk2_0,esk3_0)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_16]), c_0_17])]), c_0_18])).
% 0.11/0.35  cnf(c_0_33, plain, (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=k6_tmap_1(X2,X1)|v2_struct_0(X2)|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.35  cnf(c_0_34, plain, (v3_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X1,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[c_0_29])).
% 0.11/0.35  cnf(c_0_35, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=k8_tmap_1(esk2_0,esk3_0)|~v1_tsep_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31])])).
% 0.11/0.35  cnf(c_0_36, negated_conjecture, (v1_tsep_1(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_32, c_0_31])).
% 0.11/0.35  cnf(c_0_37, plain, (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,u1_struct_0(X2))|v2_struct_0(X1)|~v3_pre_topc(u1_struct_0(X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_33, c_0_11])).
% 0.11/0.35  cnf(c_0_38, plain, (v3_pre_topc(u1_struct_0(X1),X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_34]), c_0_11])).
% 0.11/0.35  cnf(c_0_39, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))!=k8_tmap_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36])])).
% 0.11/0.35  cnf(c_0_40, plain, (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,u1_struct_0(X2))|v2_struct_0(X1)|~v1_tsep_1(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.11/0.35  cnf(c_0_41, negated_conjecture, (k6_tmap_1(esk2_0,u1_struct_0(X1))!=k8_tmap_1(esk2_0,esk3_0)|~v1_tsep_1(X1,esk2_0)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_16]), c_0_17])]), c_0_18])).
% 0.11/0.35  cnf(c_0_42, negated_conjecture, (k8_tmap_1(esk2_0,X1)!=k8_tmap_1(esk2_0,esk3_0)|~v1_tsep_1(X1,esk2_0)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_28]), c_0_16]), c_0_17])]), c_0_18])).
% 0.11/0.35  cnf(c_0_43, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_36]), c_0_31])]), ['proof']).
% 0.11/0.35  # SZS output end CNFRefutation
% 0.11/0.35  # Proof object total steps             : 44
% 0.11/0.35  # Proof object clause steps            : 31
% 0.11/0.35  # Proof object formula steps           : 13
% 0.11/0.35  # Proof object conjectures             : 18
% 0.11/0.35  # Proof object clause conjectures      : 15
% 0.11/0.35  # Proof object formula conjectures     : 3
% 0.11/0.35  # Proof object initial clauses used    : 15
% 0.11/0.35  # Proof object initial formulas used   : 6
% 0.11/0.35  # Proof object generating inferences   : 10
% 0.11/0.35  # Proof object simplifying inferences  : 36
% 0.11/0.35  # Training examples: 0 positive, 0 negative
% 0.11/0.35  # Parsed axioms                        : 6
% 0.11/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.35  # Initial clauses                      : 21
% 0.11/0.35  # Removed in clause preprocessing      : 1
% 0.11/0.35  # Initial clauses in saturation        : 20
% 0.11/0.35  # Processed clauses                    : 37
% 0.11/0.35  # ...of these trivial                  : 1
% 0.11/0.35  # ...subsumed                          : 3
% 0.11/0.35  # ...remaining for further processing  : 33
% 0.11/0.35  # Other redundant clauses eliminated   : 5
% 0.11/0.35  # Clauses deleted for lack of memory   : 0
% 0.11/0.35  # Backward-subsumed                    : 0
% 0.11/0.35  # Backward-rewritten                   : 5
% 0.11/0.35  # Generated clauses                    : 28
% 0.11/0.35  # ...of the previous two non-trivial   : 25
% 0.11/0.35  # Contextual simplify-reflections      : 6
% 0.11/0.35  # Paramodulations                      : 24
% 0.11/0.35  # Factorizations                       : 0
% 0.11/0.35  # Equation resolutions                 : 5
% 0.11/0.35  # Propositional unsat checks           : 0
% 0.11/0.35  #    Propositional check models        : 0
% 0.11/0.35  #    Propositional check unsatisfiable : 0
% 0.11/0.35  #    Propositional clauses             : 0
% 0.11/0.35  #    Propositional clauses after purity: 0
% 0.11/0.35  #    Propositional unsat core size     : 0
% 0.11/0.35  #    Propositional preprocessing time  : 0.000
% 0.11/0.35  #    Propositional encoding time       : 0.000
% 0.11/0.35  #    Propositional solver time         : 0.000
% 0.11/0.35  #    Success case prop preproc time    : 0.000
% 0.11/0.35  #    Success case prop encoding time   : 0.000
% 0.11/0.35  #    Success case prop solver time     : 0.000
% 0.11/0.35  # Current number of processed clauses  : 25
% 0.11/0.35  #    Positive orientable unit clauses  : 4
% 0.11/0.35  #    Positive unorientable unit clauses: 0
% 0.11/0.35  #    Negative unit clauses             : 3
% 0.11/0.35  #    Non-unit-clauses                  : 18
% 0.11/0.35  # Current number of unprocessed clauses: 7
% 0.11/0.35  # ...number of literals in the above   : 56
% 0.11/0.35  # Current number of archived formulas  : 0
% 0.11/0.35  # Current number of archived clauses   : 5
% 0.11/0.35  # Clause-clause subsumption calls (NU) : 132
% 0.11/0.35  # Rec. Clause-clause subsumption calls : 11
% 0.11/0.35  # Non-unit clause-clause subsumptions  : 8
% 0.11/0.35  # Unit Clause-clause subsumption calls : 0
% 0.11/0.35  # Rewrite failures with RHS unbound    : 0
% 0.11/0.35  # BW rewrite match attempts            : 1
% 0.11/0.35  # BW rewrite match successes           : 1
% 0.11/0.35  # Condensation attempts                : 0
% 0.11/0.35  # Condensation successes               : 0
% 0.11/0.35  # Termbank termtop insertions          : 2855
% 0.11/0.35  
% 0.11/0.35  # -------------------------------------------------
% 0.11/0.35  # User time                : 0.034 s
% 0.11/0.35  # System time              : 0.000 s
% 0.11/0.35  # Total time               : 0.034 s
% 0.11/0.35  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
