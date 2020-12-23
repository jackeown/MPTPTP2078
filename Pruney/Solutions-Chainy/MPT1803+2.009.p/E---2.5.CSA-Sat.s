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
% DateTime   : Thu Dec  3 11:18:27 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  153 (15848 expanded)
%              Number of clauses        :  126 (5402 expanded)
%              Number of leaves         :   13 (4085 expanded)
%              Depth                    :   12
%              Number of atoms          :  727 (101417 expanded)
%              Number of equality atoms :   69 (5066 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t104_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
            & u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t119_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => r1_tmap_1(X2,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_tmap_1)).

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

fof(d10_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

fof(dt_k7_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_funct_1(k7_tmap_1(X1,X2))
        & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
        & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(redefinition_r1_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X4)
        & v1_funct_1(X5)
        & v1_funct_2(X5,X1,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & v1_funct_2(X6,X3,X4)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( r1_funct_2(X1,X2,X3,X4,X5,X6)
      <=> X5 = X6 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(dt_k9_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_funct_1(k9_tmap_1(X1,X2))
        & v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
        & m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_tmap_1)).

fof(t110_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( u1_struct_0(X3) = X2
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X3))
                   => r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_tmap_1)).

fof(t117_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(X1),k9_tmap_1(X1,X2),k3_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_tmap_1)).

fof(c_0_13,plain,(
    ! [X28,X29] :
      ( ( u1_struct_0(k6_tmap_1(X28,X29)) = u1_struct_0(X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( u1_pre_topc(k6_tmap_1(X28,X29)) = k5_tmap_1(X28,X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

fof(c_0_14,plain,(
    ! [X36,X37] :
      ( ~ l1_pre_topc(X36)
      | ~ m1_pre_topc(X37,X36)
      | m1_subset_1(u1_struct_0(X37),k1_zfmisc_1(u1_struct_0(X36))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => r1_tmap_1(X2,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t119_tmap_1])).

fof(c_0_16,plain,(
    ! [X17,X18,X19,X20] :
      ( ( X19 != k8_tmap_1(X17,X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X17)))
        | X20 != u1_struct_0(X18)
        | X19 = k6_tmap_1(X17,X20)
        | ~ v1_pre_topc(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( m1_subset_1(esk1_3(X17,X18,X19),k1_zfmisc_1(u1_struct_0(X17)))
        | X19 = k8_tmap_1(X17,X18)
        | ~ v1_pre_topc(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( esk1_3(X17,X18,X19) = u1_struct_0(X18)
        | X19 = k8_tmap_1(X17,X18)
        | ~ v1_pre_topc(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( X19 != k6_tmap_1(X17,esk1_3(X17,X18,X19))
        | X19 = k8_tmap_1(X17,X18)
        | ~ v1_pre_topc(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_17,plain,(
    ! [X24,X25] :
      ( ( v1_pre_topc(k8_tmap_1(X24,X25))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24)
        | ~ m1_pre_topc(X25,X24) )
      & ( v2_pre_topc(k8_tmap_1(X24,X25))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24)
        | ~ m1_pre_topc(X25,X24) )
      & ( l1_pre_topc(k8_tmap_1(X24,X25))
        | v2_struct_0(X24)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24)
        | ~ m1_pre_topc(X25,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

cnf(c_0_18,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_19,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

fof(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & ~ r1_tmap_1(esk3_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

cnf(c_0_21,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_23,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_24,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

fof(c_0_25,plain,(
    ! [X15,X16] :
      ( v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | k7_tmap_1(X15,X16) = k6_partfun1(u1_struct_0(X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).

cnf(c_0_26,plain,
    ( u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_31,plain,
    ( k6_tmap_1(X1,u1_struct_0(X2)) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_21])]),c_0_22]),c_0_19]),c_0_23]),c_0_24]),
    [final]).

fof(c_0_32,plain,(
    ! [X22,X23] :
      ( ( v1_funct_1(k7_tmap_1(X22,X23))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22))) )
      & ( v1_funct_2(k7_tmap_1(X22,X23),u1_struct_0(X22),u1_struct_0(k6_tmap_1(X22,X23)))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22))) )
      & ( m1_subset_1(k7_tmap_1(X22,X23),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k6_tmap_1(X22,X23)))))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) = u1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( k6_tmap_1(esk2_0,u1_struct_0(esk3_0)) = k8_tmap_1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_27]),c_0_28]),c_0_29])]),c_0_30]),
    [final]).

cnf(c_0_36,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_32]),
    [final]).

cnf(c_0_37,plain,
    ( k7_tmap_1(X1,u1_struct_0(X2)) = k6_partfun1(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_19]),
    [final]).

cnf(c_0_38,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_32]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk2_0,esk3_0)) = u1_struct_0(esk2_0) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_27]),c_0_28]),c_0_29])]),c_0_30]),
    [final]).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_27]),c_0_28]),c_0_29])]),c_0_30]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1))
    | v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_34])).

cnf(c_0_43,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_32]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1)) = u1_struct_0(esk2_0)
    | v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_34])).

fof(c_0_45,plain,(
    ! [X8] :
      ( v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | ~ v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_46,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_47,negated_conjecture,
    ( k7_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1) = k6_partfun1(u1_struct_0(esk2_0))
    | v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_27]),c_0_28]),c_0_29])]),c_0_30]),
    [final]).

fof(c_0_49,plain,(
    ! [X9,X10,X11,X12,X13,X14] :
      ( ( ~ r1_funct_2(X9,X10,X11,X12,X13,X14)
        | X13 = X14
        | v1_xboole_0(X10)
        | v1_xboole_0(X12)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X9,X10)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( X13 != X14
        | r1_funct_2(X9,X10,X11,X12,X13,X14)
        | v1_xboole_0(X10)
        | v1_xboole_0(X12)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X9,X10)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1)))))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41])]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_35]),c_0_35]),c_0_35]),c_0_40]),c_0_35]),c_0_41])]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1)))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_39]),c_0_40]),c_0_41])]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1)) = u1_struct_0(esk2_0)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_35]),c_0_35]),c_0_35]),c_0_40]),c_0_35]),c_0_41])]),
    [final]).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45]),
    [final]).

cnf(c_0_55,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( k7_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_57,plain,
    ( r1_funct_2(X3,X4,X5,X6,X1,X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X6)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X5,X6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))))))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_19]),c_0_29])]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_19]),c_0_29])]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_19]),c_0_29])]),
    [final]).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))) = u1_struct_0(esk2_0)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_19]),c_0_29])]),
    [final]).

cnf(c_0_62,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55]),
    [final]).

fof(c_0_63,plain,(
    ! [X26,X27] :
      ( ( v1_funct_1(k9_tmap_1(X26,X27))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_pre_topc(X27,X26) )
      & ( v1_funct_2(k9_tmap_1(X26,X27),u1_struct_0(X26),u1_struct_0(k8_tmap_1(X26,X27)))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_pre_topc(X27,X26) )
      & ( m1_subset_1(k9_tmap_1(X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(k8_tmap_1(X26,X27)))))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_pre_topc(X27,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

cnf(c_0_64,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_35]),c_0_35]),c_0_35]),c_0_40]),c_0_35]),c_0_41])]),
    [final]).

cnf(c_0_65,plain,
    ( r1_funct_2(X1,X2,X3,X4,X5,X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X5,X3,X4)
    | ~ v1_funct_2(X5,X1,X2)
    | ~ v1_funct_1(X5) ),
    inference(er,[status(thm)],[c_0_57]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_27]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_27]),
    [final]).

cnf(c_0_68,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_27]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))) = u1_struct_0(esk2_0)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_27]),
    [final]).

cnf(c_0_70,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ v1_xboole_0(u1_struct_0(esk2_0))
    | ~ l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_34])).

cnf(c_0_71,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63]),
    [final]).

cnf(c_0_72,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63]),
    [final]).

fof(c_0_73,plain,(
    ! [X30,X31,X32,X33] :
      ( v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | v2_struct_0(X32)
      | ~ m1_pre_topc(X32,X30)
      | u1_struct_0(X32) != X31
      | ~ m1_subset_1(X33,u1_struct_0(X32))
      | r1_tmap_1(X32,k6_tmap_1(X30,X31),k2_tmap_1(X30,k6_tmap_1(X30,X31),k7_tmap_1(X30,X31),X32),X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t110_tmap_1])])])])).

cnf(c_0_74,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_19]),c_0_29])]),
    [final]).

cnf(c_0_75,plain,
    ( m1_subset_1(k7_tmap_1(X1,u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_19]),
    [final]).

cnf(c_0_76,plain,
    ( v1_funct_2(k7_tmap_1(X1,u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_19]),
    [final]).

cnf(c_0_77,plain,
    ( v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_19]),
    [final]).

cnf(c_0_78,negated_conjecture,
    ( r1_funct_2(X1,X2,u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))
    | v1_xboole_0(X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1,X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_68]),
    [final]).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_69]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),u1_struct_0(esk2_0),u1_struct_0(esk2_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69]),
    [final]).

cnf(c_0_81,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_35]),c_0_35]),c_0_41])]),
    [final]).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_83,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_84,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63]),
    [final]).

cnf(c_0_85,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_86,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X3)
    | r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | u1_struct_0(X3) != X2
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_87,negated_conjecture,
    ( k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_27]),
    [final]).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_27]),c_0_35]),c_0_39]),c_0_28]),c_0_29])]),c_0_30]),
    [final]).

cnf(c_0_89,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),u1_struct_0(esk2_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_27]),c_0_35]),c_0_39]),c_0_28]),c_0_29])]),c_0_30]),
    [final]).

cnf(c_0_90,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_27]),c_0_28]),c_0_29])]),c_0_30]),
    [final]).

cnf(c_0_91,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_81]),
    [final]).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_82,c_0_39]),
    [final]).

cnf(c_0_93,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_83,c_0_39]),
    [final]).

cnf(c_0_94,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_27]),c_0_28]),c_0_29])]),c_0_30]),
    [final]).

cnf(c_0_95,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1)) = k5_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_39]),c_0_40]),c_0_41])]),
    [final]).

cnf(c_0_96,plain,
    ( r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(X1)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(X1)),k7_tmap_1(X2,u1_struct_0(X1)),X1),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_86]),c_0_19]),
    [final]).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_98,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

fof(c_0_99,plain,(
    ! [X34,X35] :
      ( v2_struct_0(X34)
      | ~ v2_pre_topc(X34)
      | ~ l1_pre_topc(X34)
      | v2_struct_0(X35)
      | ~ m1_pre_topc(X35,X34)
      | r1_funct_2(u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35)),u1_struct_0(X34),u1_struct_0(X34),k9_tmap_1(X34,X35),k3_struct_0(X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_tmap_1])])])])).

cnf(c_0_100,negated_conjecture,
    ( r1_funct_2(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | v1_xboole_0(X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1,X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_79]),c_0_67]),c_0_80]),c_0_81]),
    [final]).

cnf(c_0_101,negated_conjecture,
    ( r1_funct_2(X1,X2,u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))
    | v1_xboole_0(X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1,X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_87]),
    [final]).

cnf(c_0_102,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_87]),
    [final]).

cnf(c_0_103,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_87]),
    [final]).

cnf(c_0_104,negated_conjecture,
    ( r1_funct_2(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | v1_xboole_0(X2)
    | ~ m1_subset_1(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_88]),c_0_89]),c_0_90])]),
    [final]).

cnf(c_0_105,plain,
    ( X5 = X6
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ r1_funct_2(X1,X2,X3,X4,X5,X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X1,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_49]),
    [final]).

cnf(c_0_106,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_69]),c_0_81]),
    [final]).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_87])).

cnf(c_0_108,negated_conjecture,
    ( r1_funct_2(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | v1_xboole_0(X2)
    | ~ m1_subset_1(k9_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(k9_tmap_1(esk2_0,esk3_0),X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_92]),c_0_93]),c_0_94])]),
    [final]).

cnf(c_0_109,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))) = k5_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_19]),c_0_29])]),
    [final]).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_34])).

cnf(c_0_111,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_pre_topc(X1,k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_34])).

cnf(c_0_112,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | X3 = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_113,plain,
    ( esk1_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_114,negated_conjecture,
    ( r1_tmap_1(esk3_0,k6_tmap_1(X1,u1_struct_0(esk3_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk3_0)),k7_tmap_1(X1,u1_struct_0(esk3_0)),esk3_0),esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98]),
    [final]).

cnf(c_0_115,plain,
    ( u1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2))) = k5_tmap_1(X1,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_19]),
    [final]).

cnf(c_0_116,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(X1),k9_tmap_1(X1,X2),k3_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_99]),
    [final]).

cnf(c_0_117,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_66]),c_0_68]),
    [final]).

cnf(c_0_118,negated_conjecture,
    ( r1_tmap_1(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),X2)
    | v2_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_69]),
    [final]).

cnf(c_0_119,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_66]),c_0_68]),
    [final]).

cnf(c_0_120,negated_conjecture,
    ( r1_funct_2(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | v1_xboole_0(X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1,X2) ),
    inference(spm,[status(thm)],[c_0_100,c_0_87]),
    [final]).

cnf(c_0_121,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_103]),
    [final]).

cnf(c_0_122,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_102]),c_0_103]),c_0_81]),
    [final]).

cnf(c_0_123,negated_conjecture,
    ( X1 = k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))
    | v1_xboole_0(X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_funct_2(X3,X2,u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),X1,k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_2(X1,X3,X2)
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_66]),c_0_67]),c_0_68]),
    [final]).

cnf(c_0_124,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_87]),
    [final]).

cnf(c_0_125,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_87]),
    [final]).

cnf(c_0_126,negated_conjecture,
    ( X1 = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))
    | v1_xboole_0(X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_funct_2(X3,X2,u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),X1,k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_2(X1,X3,X2)
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_102]),c_0_90])]),c_0_103]),
    [final]).

cnf(c_0_127,negated_conjecture,
    ( X1 = k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))
    | v1_xboole_0(X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_funct_2(X3,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),X1,k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_2(X1,X3,X2)
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_79]),c_0_67]),c_0_80]),c_0_81]),
    [final]).

cnf(c_0_128,negated_conjecture,
    ( X1 = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | v1_xboole_0(X2)
    | ~ r1_funct_2(X3,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),X1,k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_2(X1,X3,X2)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_88]),c_0_89]),c_0_90])]),
    [final]).

cnf(c_0_129,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_88]),c_0_89])]),
    [final]).

cnf(c_0_130,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1)))))
    | v2_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ v2_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ l1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_69]),
    [final]).

cnf(c_0_131,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1)))
    | v2_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ v2_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ l1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_69]),
    [final]).

cnf(c_0_132,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1)) = k5_tmap_1(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1)
    | v2_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ v2_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ l1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_69]),
    [final]).

cnf(c_0_133,negated_conjecture,
    ( r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k8_tmap_1(esk2_0,esk3_0)),X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_39]),
    [final]).

cnf(c_0_134,negated_conjecture,
    ( X1 = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v1_xboole_0(X2)
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ r1_funct_2(X3,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),X1,k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_2(X1,X3,X2)
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_107]),c_0_90])]),c_0_89])]),c_0_81]),
    [final]).

cnf(c_0_135,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1))
    | v2_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ v2_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ l1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_69]),
    [final]).

cnf(c_0_136,negated_conjecture,
    ( k7_tmap_1(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1) = k7_tmap_1(esk2_0,u1_struct_0(esk3_0))
    | v2_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ v2_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ l1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_69]),c_0_48]),
    [final]).

cnf(c_0_137,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1)) = u1_struct_0(esk2_0)
    | v2_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ v2_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ l1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_69]),
    [final]).

cnf(c_0_138,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_92]),c_0_93])]),
    [final]).

cnf(c_0_139,negated_conjecture,
    ( X1 = k9_tmap_1(esk2_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | v1_xboole_0(X2)
    | ~ r1_funct_2(X3,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),X1,k9_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_2(X1,X3,X2)
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_92]),c_0_93]),c_0_94])]),
    [final]).

cnf(c_0_140,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))
    | ~ l1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_69]),
    [final]).

cnf(c_0_141,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))) = k5_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_27]),
    [final]).

cnf(c_0_142,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_69]),
    [final]).

cnf(c_0_143,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[c_0_110,c_0_35]),
    [final]).

cnf(c_0_144,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_35]),c_0_35]),c_0_41])]),
    [final]).

cnf(c_0_145,negated_conjecture,
    ( X1 = k8_tmap_1(esk2_0,esk3_0)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_27]),c_0_28]),c_0_29])]),c_0_30]),
    [final]).

cnf(c_0_146,negated_conjecture,
    ( esk1_3(esk2_0,esk3_0,X1) = u1_struct_0(esk3_0)
    | X1 = k8_tmap_1(esk2_0,esk3_0)
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_27]),c_0_28]),c_0_29])]),c_0_30]),
    [final]).

cnf(c_0_147,plain,
    ( X1 = k8_tmap_1(X2,X3)
    | v2_struct_0(X2)
    | X1 != k6_tmap_1(X2,esk1_3(X2,X3,X1))
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_148,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_149,negated_conjecture,
    ( r1_tmap_1(esk3_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk3_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_27]),c_0_35]),c_0_35]),c_0_28]),c_0_29])]),c_0_30]),
    [final]).

cnf(c_0_150,negated_conjecture,
    ( u1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) = k5_tmap_1(esk2_0,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_27]),c_0_35]),c_0_28]),c_0_29])]),c_0_30]),
    [final]).

cnf(c_0_151,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k3_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_27]),c_0_39]),c_0_28]),c_0_29])]),c_0_98]),c_0_30]),
    [final]).

cnf(c_0_152,negated_conjecture,
    ( v1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_27]),c_0_28]),c_0_29])]),c_0_30]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:52:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.041 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # No proof found!
% 0.20/0.40  # SZS status CounterSatisfiable
% 0.20/0.40  # SZS output start Saturation
% 0.20/0.40  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.20/0.40  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.20/0.40  fof(t119_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>r1_tmap_1(X2,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_tmap_1)).
% 0.20/0.40  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_tmap_1)).
% 0.20/0.40  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.20/0.40  fof(d10_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_tmap_1)).
% 0.20/0.40  fof(dt_k7_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 0.20/0.40  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.20/0.40  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.40  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 0.20/0.40  fof(dt_k9_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_tmap_1)).
% 0.20/0.40  fof(t110_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(u1_struct_0(X3)=X2=>![X4]:(m1_subset_1(X4,u1_struct_0(X3))=>r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_tmap_1)).
% 0.20/0.40  fof(t117_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(X1),k9_tmap_1(X1,X2),k3_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_tmap_1)).
% 0.20/0.40  fof(c_0_13, plain, ![X28, X29]:((u1_struct_0(k6_tmap_1(X28,X29))=u1_struct_0(X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)))&(u1_pre_topc(k6_tmap_1(X28,X29))=k5_tmap_1(X28,X29)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.20/0.40  fof(c_0_14, plain, ![X36, X37]:(~l1_pre_topc(X36)|(~m1_pre_topc(X37,X36)|m1_subset_1(u1_struct_0(X37),k1_zfmisc_1(u1_struct_0(X36))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.20/0.40  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>r1_tmap_1(X2,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X3))))), inference(assume_negation,[status(cth)],[t119_tmap_1])).
% 0.20/0.40  fof(c_0_16, plain, ![X17, X18, X19, X20]:((X19!=k8_tmap_1(X17,X18)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X17)))|(X20!=u1_struct_0(X18)|X19=k6_tmap_1(X17,X20)))|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&((m1_subset_1(esk1_3(X17,X18,X19),k1_zfmisc_1(u1_struct_0(X17)))|X19=k8_tmap_1(X17,X18)|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&((esk1_3(X17,X18,X19)=u1_struct_0(X18)|X19=k8_tmap_1(X17,X18)|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(X19!=k6_tmap_1(X17,esk1_3(X17,X18,X19))|X19=k8_tmap_1(X17,X18)|(~v1_pre_topc(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|~m1_pre_topc(X18,X17)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 0.20/0.40  fof(c_0_17, plain, ![X24, X25]:(((v1_pre_topc(k8_tmap_1(X24,X25))|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|~m1_pre_topc(X25,X24)))&(v2_pre_topc(k8_tmap_1(X24,X25))|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|~m1_pre_topc(X25,X24))))&(l1_pre_topc(k8_tmap_1(X24,X25))|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|~m1_pre_topc(X25,X24)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.20/0.40  cnf(c_0_18, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.20/0.40  cnf(c_0_19, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.20/0.40  fof(c_0_20, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&~r1_tmap_1(esk3_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.20/0.40  cnf(c_0_21, plain, (X1=k6_tmap_1(X2,X4)|v2_struct_0(X2)|X1!=k8_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_22, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.20/0.40  cnf(c_0_23, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.20/0.40  cnf(c_0_24, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.20/0.40  fof(c_0_25, plain, ![X15, X16]:(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|k7_tmap_1(X15,X16)=k6_partfun1(u1_struct_0(X15)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).
% 0.20/0.40  cnf(c_0_26, plain, (u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2)))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19]), ['final']).
% 0.20/0.40  cnf(c_0_27, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.20/0.40  cnf(c_0_28, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.20/0.40  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.20/0.40  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.20/0.40  cnf(c_0_31, plain, (k6_tmap_1(X1,u1_struct_0(X2))=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_21])]), c_0_22]), c_0_19]), c_0_23]), c_0_24]), ['final']).
% 0.20/0.40  fof(c_0_32, plain, ![X22, X23]:(((v1_funct_1(k7_tmap_1(X22,X23))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))))&(v1_funct_2(k7_tmap_1(X22,X23),u1_struct_0(X22),u1_struct_0(k6_tmap_1(X22,X23)))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22))))))&(m1_subset_1(k7_tmap_1(X22,X23),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(k6_tmap_1(X22,X23)))))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).
% 0.20/0.40  cnf(c_0_33, plain, (v2_struct_0(X1)|k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_25]), ['final']).
% 0.20/0.40  cnf(c_0_34, negated_conjecture, (u1_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))=u1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.20/0.40  cnf(c_0_35, negated_conjecture, (k6_tmap_1(esk2_0,u1_struct_0(esk3_0))=k8_tmap_1(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_27]), c_0_28]), c_0_29])]), c_0_30]), ['final']).
% 0.20/0.40  cnf(c_0_36, plain, (v1_funct_1(k7_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_32]), ['final']).
% 0.20/0.40  cnf(c_0_37, plain, (k7_tmap_1(X1,u1_struct_0(X2))=k6_partfun1(u1_struct_0(X1))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_33, c_0_19]), ['final']).
% 0.20/0.40  cnf(c_0_38, plain, (m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_32]), ['final']).
% 0.20/0.40  cnf(c_0_39, negated_conjecture, (u1_struct_0(k8_tmap_1(esk2_0,esk3_0))=u1_struct_0(esk2_0)), inference(rw,[status(thm)],[c_0_34, c_0_35]), ['final']).
% 0.20/0.40  cnf(c_0_40, negated_conjecture, (v2_pre_topc(k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_27]), c_0_28]), c_0_29])]), c_0_30]), ['final']).
% 0.20/0.40  cnf(c_0_41, negated_conjecture, (l1_pre_topc(k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_27]), c_0_28]), c_0_29])]), c_0_30]), ['final']).
% 0.20/0.40  cnf(c_0_42, negated_conjecture, (v1_funct_1(k7_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1))|v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_36, c_0_34])).
% 0.20/0.40  cnf(c_0_43, plain, (v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_32]), ['final']).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (u1_struct_0(k6_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1))=u1_struct_0(esk2_0)|v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_18, c_0_34])).
% 0.20/0.40  fof(c_0_45, plain, ![X8]:(v2_struct_0(X8)|~l1_struct_0(X8)|~v1_xboole_0(u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.20/0.40  fof(c_0_46, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, (k7_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1)=k6_partfun1(u1_struct_0(esk2_0))|v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.40  cnf(c_0_48, negated_conjecture, (k6_partfun1(u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_27]), c_0_28]), c_0_29])]), c_0_30]), ['final']).
% 0.20/0.40  fof(c_0_49, plain, ![X9, X10, X11, X12, X13, X14]:((~r1_funct_2(X9,X10,X11,X12,X13,X14)|X13=X14|(v1_xboole_0(X10)|v1_xboole_0(X12)|~v1_funct_1(X13)|~v1_funct_2(X13,X9,X10)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|~v1_funct_1(X14)|~v1_funct_2(X14,X11,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))&(X13!=X14|r1_funct_2(X9,X10,X11,X12,X13,X14)|(v1_xboole_0(X10)|v1_xboole_0(X12)|~v1_funct_1(X13)|~v1_funct_2(X13,X9,X10)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|~v1_funct_1(X14)|~v1_funct_2(X14,X11,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 0.20/0.40  cnf(c_0_50, negated_conjecture, (m1_subset_1(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1)))))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41])]), ['final']).
% 0.20/0.40  cnf(c_0_51, negated_conjecture, (v1_funct_1(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_35]), c_0_35]), c_0_35]), c_0_40]), c_0_35]), c_0_41])]), ['final']).
% 0.20/0.40  cnf(c_0_52, negated_conjecture, (v1_funct_2(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1)))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_39]), c_0_40]), c_0_41])]), ['final']).
% 0.20/0.40  cnf(c_0_53, negated_conjecture, (u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1))=u1_struct_0(esk2_0)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_35]), c_0_35]), c_0_35]), c_0_40]), c_0_35]), c_0_41])]), ['final']).
% 0.20/0.40  cnf(c_0_54, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_45]), ['final']).
% 0.20/0.40  cnf(c_0_55, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46]), ['final']).
% 0.20/0.40  cnf(c_0_56, negated_conjecture, (k7_tmap_1(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1)=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~v2_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.40  cnf(c_0_57, plain, (r1_funct_2(X3,X4,X5,X6,X1,X2)|v1_xboole_0(X4)|v1_xboole_0(X6)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X5,X6)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.40  cnf(c_0_58, negated_conjecture, (m1_subset_1(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))))))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_19]), c_0_29])]), ['final']).
% 0.20/0.40  cnf(c_0_59, negated_conjecture, (v1_funct_1(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_19]), c_0_29])]), ['final']).
% 0.20/0.40  cnf(c_0_60, negated_conjecture, (v1_funct_2(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_19]), c_0_29])]), ['final']).
% 0.20/0.40  cnf(c_0_61, negated_conjecture, (u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)))=u1_struct_0(esk2_0)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_19]), c_0_29])]), ['final']).
% 0.20/0.40  cnf(c_0_62, plain, (v2_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_54, c_0_55]), ['final']).
% 0.20/0.40  fof(c_0_63, plain, ![X26, X27]:(((v1_funct_1(k9_tmap_1(X26,X27))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_pre_topc(X27,X26)))&(v1_funct_2(k9_tmap_1(X26,X27),u1_struct_0(X26),u1_struct_0(k8_tmap_1(X26,X27)))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_pre_topc(X27,X26))))&(m1_subset_1(k9_tmap_1(X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(k8_tmap_1(X26,X27)))))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_pre_topc(X27,X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).
% 0.20/0.40  cnf(c_0_64, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1)=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_35]), c_0_35]), c_0_35]), c_0_40]), c_0_35]), c_0_41])]), ['final']).
% 0.20/0.40  cnf(c_0_65, plain, (r1_funct_2(X1,X2,X3,X4,X5,X5)|v1_xboole_0(X4)|v1_xboole_0(X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(X5,X3,X4)|~v1_funct_2(X5,X1,X2)|~v1_funct_1(X5)), inference(er,[status(thm)],[c_0_57]), ['final']).
% 0.20/0.40  cnf(c_0_66, negated_conjecture, (m1_subset_1(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_58, c_0_27]), ['final']).
% 0.20/0.40  cnf(c_0_67, negated_conjecture, (v1_funct_1(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_59, c_0_27]), ['final']).
% 0.20/0.40  cnf(c_0_68, negated_conjecture, (v1_funct_2(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_60, c_0_27]), ['final']).
% 0.20/0.40  cnf(c_0_69, negated_conjecture, (u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))=u1_struct_0(esk2_0)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_61, c_0_27]), ['final']).
% 0.20/0.40  cnf(c_0_70, negated_conjecture, (v2_struct_0(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~v1_xboole_0(u1_struct_0(esk2_0))|~l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_62, c_0_34])).
% 0.20/0.40  cnf(c_0_71, plain, (m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63]), ['final']).
% 0.20/0.40  cnf(c_0_72, plain, (v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63]), ['final']).
% 0.20/0.40  fof(c_0_73, plain, ![X30, X31, X32, X33]:(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|(v2_struct_0(X32)|~m1_pre_topc(X32,X30)|(u1_struct_0(X32)!=X31|(~m1_subset_1(X33,u1_struct_0(X32))|r1_tmap_1(X32,k6_tmap_1(X30,X31),k2_tmap_1(X30,k6_tmap_1(X30,X31),k7_tmap_1(X30,X31),X32),X33)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t110_tmap_1])])])])).
% 0.20/0.40  cnf(c_0_74, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_19]), c_0_29])]), ['final']).
% 0.20/0.40  cnf(c_0_75, plain, (m1_subset_1(k7_tmap_1(X1,u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_38, c_0_19]), ['final']).
% 0.20/0.40  cnf(c_0_76, plain, (v1_funct_2(k7_tmap_1(X1,u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_43, c_0_19]), ['final']).
% 0.20/0.40  cnf(c_0_77, plain, (v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_36, c_0_19]), ['final']).
% 0.20/0.40  cnf(c_0_78, negated_conjecture, (r1_funct_2(X1,X2,u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|v1_xboole_0(u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))|v1_xboole_0(X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_subset_1(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1,X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_68]), ['final']).
% 0.20/0.40  cnf(c_0_79, negated_conjecture, (m1_subset_1(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_66, c_0_69]), ['final']).
% 0.20/0.40  cnf(c_0_80, negated_conjecture, (v1_funct_2(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),u1_struct_0(esk2_0),u1_struct_0(esk2_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_68, c_0_69]), ['final']).
% 0.20/0.40  cnf(c_0_81, negated_conjecture, (v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_35]), c_0_35]), c_0_41])]), ['final']).
% 0.20/0.40  cnf(c_0_82, negated_conjecture, (m1_subset_1(k9_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.20/0.40  cnf(c_0_83, negated_conjecture, (v1_funct_2(k9_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.20/0.40  cnf(c_0_84, plain, (v1_funct_1(k9_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_63]), ['final']).
% 0.20/0.40  cnf(c_0_85, plain, (u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.20/0.40  cnf(c_0_86, plain, (v2_struct_0(X1)|v2_struct_0(X3)|r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X3,X1)|u1_struct_0(X3)!=X2|~m1_subset_1(X4,u1_struct_0(X3))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.20/0.40  cnf(c_0_87, negated_conjecture, (k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_74, c_0_27]), ['final']).
% 0.20/0.40  cnf(c_0_88, negated_conjecture, (m1_subset_1(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_27]), c_0_35]), c_0_39]), c_0_28]), c_0_29])]), c_0_30]), ['final']).
% 0.20/0.40  cnf(c_0_89, negated_conjecture, (v1_funct_2(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),u1_struct_0(esk2_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_27]), c_0_35]), c_0_39]), c_0_28]), c_0_29])]), c_0_30]), ['final']).
% 0.20/0.40  cnf(c_0_90, negated_conjecture, (v1_funct_1(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_27]), c_0_28]), c_0_29])]), c_0_30]), ['final']).
% 0.20/0.40  cnf(c_0_91, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|v1_xboole_0(u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80]), c_0_81]), ['final']).
% 0.20/0.40  cnf(c_0_92, negated_conjecture, (m1_subset_1(k9_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(rw,[status(thm)],[c_0_82, c_0_39]), ['final']).
% 0.20/0.40  cnf(c_0_93, negated_conjecture, (v1_funct_2(k9_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_83, c_0_39]), ['final']).
% 0.20/0.40  cnf(c_0_94, negated_conjecture, (v1_funct_1(k9_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_27]), c_0_28]), c_0_29])]), c_0_30]), ['final']).
% 0.20/0.40  cnf(c_0_95, negated_conjecture, (u1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1))=k5_tmap_1(k8_tmap_1(esk2_0,esk3_0),X1)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_39]), c_0_40]), c_0_41])]), ['final']).
% 0.20/0.40  cnf(c_0_96, plain, (r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(X1)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(X1)),k7_tmap_1(X2,u1_struct_0(X1)),X1),X3)|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_86]), c_0_19]), ['final']).
% 0.20/0.40  cnf(c_0_97, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.20/0.40  cnf(c_0_98, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.20/0.40  fof(c_0_99, plain, ![X34, X35]:(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|(v2_struct_0(X35)|~m1_pre_topc(X35,X34)|r1_funct_2(u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35)),u1_struct_0(X34),u1_struct_0(X34),k9_tmap_1(X34,X35),k3_struct_0(X34)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_tmap_1])])])])).
% 0.20/0.40  cnf(c_0_100, negated_conjecture, (r1_funct_2(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|v1_xboole_0(X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_subset_1(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1,X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_79]), c_0_67]), c_0_80]), c_0_81]), ['final']).
% 0.20/0.40  cnf(c_0_101, negated_conjecture, (r1_funct_2(X1,X2,u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))|v1_xboole_0(u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))|v1_xboole_0(X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_subset_1(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1,X2)), inference(spm,[status(thm)],[c_0_78, c_0_87]), ['final']).
% 0.20/0.40  cnf(c_0_102, negated_conjecture, (m1_subset_1(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_66, c_0_87]), ['final']).
% 0.20/0.40  cnf(c_0_103, negated_conjecture, (v1_funct_2(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_68, c_0_87]), ['final']).
% 0.20/0.40  cnf(c_0_104, negated_conjecture, (r1_funct_2(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))|v1_xboole_0(u1_struct_0(esk2_0))|v1_xboole_0(X2)|~m1_subset_1(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_88]), c_0_89]), c_0_90])]), ['final']).
% 0.20/0.40  cnf(c_0_105, plain, (X5=X6|v1_xboole_0(X2)|v1_xboole_0(X4)|~r1_funct_2(X1,X2,X3,X4,X5,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,X1,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_49]), ['final']).
% 0.20/0.40  cnf(c_0_106, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_69]), c_0_81]), ['final']).
% 0.20/0.40  cnf(c_0_107, negated_conjecture, (m1_subset_1(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_79, c_0_87])).
% 0.20/0.40  cnf(c_0_108, negated_conjecture, (r1_funct_2(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))|v1_xboole_0(X2)|~m1_subset_1(k9_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(k9_tmap_1(esk2_0,esk3_0),X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_92]), c_0_93]), c_0_94])]), ['final']).
% 0.20/0.40  cnf(c_0_109, negated_conjecture, (u1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)))=k5_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_19]), c_0_29])]), ['final']).
% 0.20/0.40  cnf(c_0_110, negated_conjecture, (m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_19, c_0_34])).
% 0.20/0.40  cnf(c_0_111, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_pre_topc(X1,k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~l1_pre_topc(k6_tmap_1(esk2_0,u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_19, c_0_34])).
% 0.20/0.40  cnf(c_0_112, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|X3=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_pre_topc(X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.20/0.40  cnf(c_0_113, plain, (esk1_3(X1,X2,X3)=u1_struct_0(X2)|X3=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_pre_topc(X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.20/0.40  cnf(c_0_114, negated_conjecture, (r1_tmap_1(esk3_0,k6_tmap_1(X1,u1_struct_0(esk3_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk3_0)),k7_tmap_1(X1,u1_struct_0(esk3_0)),esk3_0),esk4_0)|v2_struct_0(X1)|~m1_pre_topc(esk3_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98]), ['final']).
% 0.20/0.40  cnf(c_0_115, plain, (u1_pre_topc(k6_tmap_1(X1,u1_struct_0(X2)))=k5_tmap_1(X1,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_85, c_0_19]), ['final']).
% 0.20/0.40  cnf(c_0_116, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(X1),k9_tmap_1(X1,X2),k3_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_99]), ['final']).
% 0.20/0.40  cnf(c_0_117, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|v1_xboole_0(u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_66]), c_0_68]), ['final']).
% 0.20/0.40  cnf(c_0_118, negated_conjecture, (r1_tmap_1(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),X2)|v2_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~m1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_96, c_0_69]), ['final']).
% 0.20/0.40  cnf(c_0_119, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|v1_xboole_0(u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_66]), c_0_68]), ['final']).
% 0.20/0.40  cnf(c_0_120, negated_conjecture, (r1_funct_2(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))|v1_xboole_0(X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_subset_1(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),X1,X2)), inference(spm,[status(thm)],[c_0_100, c_0_87]), ['final']).
% 0.20/0.40  cnf(c_0_121, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))|v1_xboole_0(u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_103]), ['final']).
% 0.20/0.40  cnf(c_0_122, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))|v1_xboole_0(u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_102]), c_0_103]), c_0_81]), ['final']).
% 0.20/0.40  cnf(c_0_123, negated_conjecture, (X1=k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))|v1_xboole_0(X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_funct_2(X3,X2,u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),X1,k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_2(X1,X3,X2)|~v1_funct_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_66]), c_0_67]), c_0_68]), ['final']).
% 0.20/0.40  cnf(c_0_124, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))|v1_xboole_0(u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_91, c_0_87]), ['final']).
% 0.20/0.40  cnf(c_0_125, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_106, c_0_87]), ['final']).
% 0.20/0.40  cnf(c_0_126, negated_conjecture, (X1=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))))|v1_xboole_0(X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_funct_2(X3,X2,u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))),X1,k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_2(X1,X3,X2)|~v1_funct_1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_102]), c_0_90])]), c_0_103]), ['final']).
% 0.20/0.40  cnf(c_0_127, negated_conjecture, (X1=k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))|v1_xboole_0(X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_funct_2(X3,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),X1,k7_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_2(X1,X3,X2)|~v1_funct_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_79]), c_0_67]), c_0_80]), c_0_81]), ['final']).
% 0.20/0.40  cnf(c_0_128, negated_conjecture, (X1=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))|v1_xboole_0(X2)|~r1_funct_2(X3,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),X1,k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_2(X1,X3,X2)|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_88]), c_0_89]), c_0_90])]), ['final']).
% 0.20/0.40  cnf(c_0_129, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_88]), c_0_89])]), ['final']).
% 0.20/0.40  cnf(c_0_130, negated_conjecture, (m1_subset_1(k7_tmap_1(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1)))))|v2_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~v2_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~l1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_38, c_0_69]), ['final']).
% 0.20/0.40  cnf(c_0_131, negated_conjecture, (v1_funct_2(k7_tmap_1(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1)))|v2_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~v2_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~l1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_43, c_0_69]), ['final']).
% 0.20/0.40  cnf(c_0_132, negated_conjecture, (u1_pre_topc(k6_tmap_1(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1))=k5_tmap_1(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1)|v2_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~v2_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~l1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_85, c_0_69]), ['final']).
% 0.20/0.40  cnf(c_0_133, negated_conjecture, (r1_tmap_1(k8_tmap_1(esk2_0,esk3_0),k6_tmap_1(X1,u1_struct_0(esk2_0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(esk2_0)),k7_tmap_1(X1,u1_struct_0(esk2_0)),k8_tmap_1(esk2_0,esk3_0)),X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_96, c_0_39]), ['final']).
% 0.20/0.40  cnf(c_0_134, negated_conjecture, (X1=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v1_xboole_0(X2)|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~r1_funct_2(X3,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),X1,k7_tmap_1(esk2_0,u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_2(X1,X3,X2)|~v1_funct_1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_107]), c_0_90])]), c_0_89])]), c_0_81]), ['final']).
% 0.20/0.40  cnf(c_0_135, negated_conjecture, (v1_funct_1(k7_tmap_1(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1))|v2_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~v2_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~l1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_36, c_0_69]), ['final']).
% 0.20/0.40  cnf(c_0_136, negated_conjecture, (k7_tmap_1(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1)=k7_tmap_1(esk2_0,u1_struct_0(esk3_0))|v2_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~v2_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~l1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_69]), c_0_48]), ['final']).
% 0.20/0.40  cnf(c_0_137, negated_conjecture, (u1_struct_0(k6_tmap_1(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1))=u1_struct_0(esk2_0)|v2_struct_0(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~v2_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~l1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_18, c_0_69]), ['final']).
% 0.20/0.40  cnf(c_0_138, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_92]), c_0_93])]), ['final']).
% 0.20/0.40  cnf(c_0_139, negated_conjecture, (X1=k9_tmap_1(esk2_0,esk3_0)|v1_xboole_0(u1_struct_0(esk2_0))|v1_xboole_0(X2)|~r1_funct_2(X3,X2,u1_struct_0(esk2_0),u1_struct_0(esk2_0),X1,k9_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_2(X1,X3,X2)|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_92]), c_0_93]), c_0_94])]), ['final']).
% 0.20/0.41  cnf(c_0_140, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(X1,k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))|~l1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_19, c_0_69]), ['final']).
% 0.20/0.41  cnf(c_0_141, negated_conjecture, (u1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)))=k5_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_109, c_0_27]), ['final']).
% 0.20/0.41  cnf(c_0_142, negated_conjecture, (m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(k8_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(k6_tmap_1(k8_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_19, c_0_69]), ['final']).
% 0.20/0.41  cnf(c_0_143, negated_conjecture, (m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(k8_tmap_1(esk2_0,esk3_0),X1)|~l1_pre_topc(X1)), inference(rw,[status(thm)],[c_0_110, c_0_35]), ['final']).
% 0.20/0.41  cnf(c_0_144, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_pre_topc(X1,k8_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_35]), c_0_35]), c_0_41])]), ['final']).
% 0.20/0.41  cnf(c_0_145, negated_conjecture, (X1=k8_tmap_1(esk2_0,esk3_0)|m1_subset_1(esk1_3(esk2_0,esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_27]), c_0_28]), c_0_29])]), c_0_30]), ['final']).
% 0.20/0.41  cnf(c_0_146, negated_conjecture, (esk1_3(esk2_0,esk3_0,X1)=u1_struct_0(esk3_0)|X1=k8_tmap_1(esk2_0,esk3_0)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_27]), c_0_28]), c_0_29])]), c_0_30]), ['final']).
% 0.20/0.41  cnf(c_0_147, plain, (X1=k8_tmap_1(X2,X3)|v2_struct_0(X2)|X1!=k6_tmap_1(X2,esk1_3(X2,X3,X1))|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.20/0.41  cnf(c_0_148, negated_conjecture, (~r1_tmap_1(esk3_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.20/0.41  cnf(c_0_149, negated_conjecture, (r1_tmap_1(esk3_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,u1_struct_0(esk3_0)),esk3_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_27]), c_0_35]), c_0_35]), c_0_28]), c_0_29])]), c_0_30]), ['final']).
% 0.20/0.41  cnf(c_0_150, negated_conjecture, (u1_pre_topc(k8_tmap_1(esk2_0,esk3_0))=k5_tmap_1(esk2_0,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_27]), c_0_35]), c_0_28]), c_0_29])]), c_0_30]), ['final']).
% 0.20/0.41  cnf(c_0_151, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),k9_tmap_1(esk2_0,esk3_0),k3_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_27]), c_0_39]), c_0_28]), c_0_29])]), c_0_98]), c_0_30]), ['final']).
% 0.20/0.41  cnf(c_0_152, negated_conjecture, (v1_pre_topc(k8_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_27]), c_0_28]), c_0_29])]), c_0_30]), ['final']).
% 0.20/0.41  # SZS output end Saturation
% 0.20/0.41  # Proof object total steps             : 153
% 0.20/0.41  # Proof object clause steps            : 126
% 0.20/0.41  # Proof object formula steps           : 27
% 0.20/0.41  # Proof object conjectures             : 96
% 0.20/0.41  # Proof object clause conjectures      : 93
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 30
% 0.20/0.41  # Proof object initial formulas used   : 13
% 0.20/0.41  # Proof object generating inferences   : 83
% 0.20/0.41  # Proof object simplifying inferences  : 185
% 0.20/0.41  # Parsed axioms                        : 13
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 30
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 30
% 0.20/0.41  # Processed clauses                    : 188
% 0.20/0.41  # ...of these trivial                  : 0
% 0.20/0.41  # ...subsumed                          : 31
% 0.20/0.41  # ...remaining for further processing  : 157
% 0.20/0.41  # Other redundant clauses eliminated   : 4
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 2
% 0.20/0.41  # Backward-rewritten                   : 10
% 0.20/0.41  # Generated clauses                    : 122
% 0.20/0.41  # ...of the previous two non-trivial   : 131
% 0.20/0.41  # Contextual simplify-reflections      : 25
% 0.20/0.41  # Paramodulations                      : 119
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 4
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 112
% 0.20/0.41  #    Positive orientable unit clauses  : 19
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 3
% 0.20/0.41  #    Non-unit-clauses                  : 90
% 0.20/0.41  # Current number of unprocessed clauses: 0
% 0.20/0.41  # ...number of literals in the above   : 0
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 42
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 4674
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 427
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 56
% 0.20/0.41  # Unit Clause-clause subsumption calls : 77
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 8
% 0.20/0.41  # BW rewrite match successes           : 5
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 10467
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.054 s
% 0.20/0.41  # System time              : 0.008 s
% 0.20/0.41  # Total time               : 0.063 s
% 0.20/0.41  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
