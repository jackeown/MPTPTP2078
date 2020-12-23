%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1799+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:46 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 142 expanded)
%              Number of clauses        :   27 (  50 expanded)
%              Number of leaves         :    6 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :  234 ( 971 expanded)
%              Number of equality atoms :   27 (  91 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t115_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_pre_topc(X3,k8_tmap_1(X1,X2))
             => ( u1_struct_0(X3) = u1_struct_0(X2)
               => ( v1_tsep_1(X3,k8_tmap_1(X1,X2))
                  & m1_pre_topc(X3,k8_tmap_1(X1,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_tmap_1)).

fof(dt_k8_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2))
        & l1_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

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

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t105_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
             => ( X3 = X2
               => v3_pre_topc(X3,k6_tmap_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( m1_pre_topc(X3,k8_tmap_1(X1,X2))
               => ( u1_struct_0(X3) = u1_struct_0(X2)
                 => ( v1_tsep_1(X3,k8_tmap_1(X1,X2))
                    & m1_pre_topc(X3,k8_tmap_1(X1,X2)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t115_tmap_1])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & m1_pre_topc(esk4_0,k8_tmap_1(esk2_0,esk3_0))
    & u1_struct_0(esk4_0) = u1_struct_0(esk3_0)
    & ( ~ v1_tsep_1(esk4_0,k8_tmap_1(esk2_0,esk3_0))
      | ~ m1_pre_topc(esk4_0,k8_tmap_1(esk2_0,esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

fof(c_0_8,plain,(
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

fof(c_0_9,plain,(
    ! [X15,X16,X17] :
      ( ( ~ v1_tsep_1(X16,X15)
        | ~ m1_pre_topc(X16,X15)
        | v3_pre_topc(X17,X15)
        | X17 != u1_struct_0(X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ m1_pre_topc(X16,X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v1_tsep_1(X16,X15)
        | ~ v3_pre_topc(X17,X15)
        | X17 != u1_struct_0(X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ m1_pre_topc(X16,X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_pre_topc(X16,X15)
        | ~ v3_pre_topc(X17,X15)
        | X17 != u1_struct_0(X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ m1_pre_topc(X16,X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).

fof(c_0_10,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,X18)
      | m1_subset_1(u1_struct_0(X19),k1_zfmisc_1(u1_struct_0(X18))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_16,plain,(
    ! [X12,X13,X14] :
      ( v2_struct_0(X12)
      | ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X12,X13))))
      | X14 != X13
      | v3_pre_topc(X14,k6_tmap_1(X12,X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t105_tmap_1])])])])).

fof(c_0_17,plain,(
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

cnf(c_0_18,negated_conjecture,
    ( ~ v1_tsep_1(esk4_0,k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(esk4_0,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( m1_pre_topc(esk4_0,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk2_0,X1))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk2_0,X1))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_15]),c_0_13]),c_0_14])])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | v3_pre_topc(X3,k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
    | X3 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_tsep_1(esk4_0,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19])])).

cnf(c_0_29,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_20]),c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_33,plain,
    ( v3_pre_topc(X1,k6_tmap_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X2,X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k6_tmap_1(X1,u1_struct_0(X2)) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_26])]),c_0_15]),c_0_12]),c_0_27]),c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( ~ v3_pre_topc(u1_struct_0(esk3_0),k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_19]),c_0_31]),c_0_32])])).

cnf(c_0_36,plain,
    ( v3_pre_topc(u1_struct_0(X1),k8_tmap_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(X2,X1))))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_21])).

cnf(c_0_37,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_23]),c_0_13]),c_0_14])]),c_0_11])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_19]),c_0_31])]),
    [proof]).

%------------------------------------------------------------------------------
