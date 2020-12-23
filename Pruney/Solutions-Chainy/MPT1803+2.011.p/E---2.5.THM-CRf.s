%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:27 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 292 expanded)
%              Number of clauses        :   42 ( 116 expanded)
%              Number of leaves         :   11 (  79 expanded)
%              Depth                    :   15
%              Number of atoms          :  448 (2237 expanded)
%              Number of equality atoms :   47 ( 192 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(d12_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))) )
             => ( X3 = k9_tmap_1(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X4 = u1_struct_0(X2)
                     => r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X4)),X3,k7_tmap_1(X1,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_tmap_1)).

fof(t104_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
            & u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(dt_k7_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_funct_1(k7_tmap_1(X1,X2))
        & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
        & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_tmap_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_11,plain,(
    ! [X15,X16,X17,X18] :
      ( ( X17 != k8_tmap_1(X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X15)))
        | X18 != u1_struct_0(X16)
        | X17 = k6_tmap_1(X15,X18)
        | ~ v1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk1_3(X15,X16,X17),k1_zfmisc_1(u1_struct_0(X15)))
        | X17 = k8_tmap_1(X15,X16)
        | ~ v1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( esk1_3(X15,X16,X17) = u1_struct_0(X16)
        | X17 = k8_tmap_1(X15,X16)
        | ~ v1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( X17 != k6_tmap_1(X15,esk1_3(X15,X16,X17))
        | X17 = k8_tmap_1(X15,X16)
        | ~ v1_pre_topc(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_12,plain,(
    ! [X27,X28] :
      ( ( v1_pre_topc(k8_tmap_1(X27,X28))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_pre_topc(X28,X27) )
      & ( v2_pre_topc(k8_tmap_1(X27,X28))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_pre_topc(X28,X27) )
      & ( l1_pre_topc(k8_tmap_1(X27,X28))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_pre_topc(X28,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

cnf(c_0_13,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X35,X36] :
      ( ~ l1_pre_topc(X35)
      | ~ m1_pre_topc(X36,X35)
      | m1_subset_1(u1_struct_0(X36),k1_zfmisc_1(u1_struct_0(X35))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_18,plain,(
    ! [X20,X21,X22,X23] :
      ( ( X22 != k9_tmap_1(X20,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))
        | X23 != u1_struct_0(X21)
        | r1_funct_2(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)),u1_struct_0(X20),u1_struct_0(k6_tmap_1(X20,X23)),X22,k7_tmap_1(X20,X23))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))))
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk2_3(X20,X21,X22),k1_zfmisc_1(u1_struct_0(X20)))
        | X22 = k9_tmap_1(X20,X21)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))))
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( esk2_3(X20,X21,X22) = u1_struct_0(X21)
        | X22 = k9_tmap_1(X20,X21)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))))
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ r1_funct_2(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)),u1_struct_0(X20),u1_struct_0(k6_tmap_1(X20,esk2_3(X20,X21,X22))),X22,k7_tmap_1(X20,esk2_3(X20,X21,X22)))
        | X22 = k9_tmap_1(X20,X21)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))))
        | ~ m1_pre_topc(X21,X20)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).

fof(c_0_19,plain,(
    ! [X29,X30] :
      ( ( u1_struct_0(k6_tmap_1(X29,X30)) = u1_struct_0(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( u1_pre_topc(k6_tmap_1(X29,X30)) = k5_tmap_1(X29,X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

cnf(c_0_20,plain,
    ( k8_tmap_1(X1,X2) = k6_tmap_1(X1,X3)
    | v2_struct_0(X1)
    | X3 != u1_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_21,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,esk2_3(X1,X2,X3))),X3,k7_tmap_1(X1,esk2_3(X1,X2,X3)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( esk2_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k6_tmap_1(X1,u1_struct_0(X2)) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_20]),c_0_21])).

cnf(c_0_26,plain,
    ( X1 = k9_tmap_1(X2,X3)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ r1_funct_2(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X2,u1_struct_0(X3))),X1,k7_tmap_1(X2,u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_21])).

fof(c_0_28,plain,(
    ! [X25,X26] :
      ( ( v1_funct_1(k7_tmap_1(X25,X26))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25))) )
      & ( v1_funct_2(k7_tmap_1(X25,X26),u1_struct_0(X25),u1_struct_0(k6_tmap_1(X25,X26)))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25))) )
      & ( m1_subset_1(k7_tmap_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(k6_tmap_1(X25,X26)))))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

cnf(c_0_29,plain,
    ( X1 = k9_tmap_1(X2,X3)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ r1_funct_2(u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X2,u1_struct_0(X3))),X1,k7_tmap_1(X2,u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X2))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_30,plain,(
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

cnf(c_0_31,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_33,negated_conjecture,(
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

cnf(c_0_34,plain,
    ( X1 = k9_tmap_1(X2,X3)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ r1_funct_2(u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)),X1,k7_tmap_1(X2,u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X2))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_25])).

cnf(c_0_35,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( v1_funct_2(k7_tmap_1(X1,u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_25]),c_0_21])).

cnf(c_0_37,plain,
    ( m1_subset_1(k7_tmap_1(X1,u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_25]),c_0_21])).

fof(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & ~ r1_tmap_1(esk4_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_33])])])])).

cnf(c_0_39,plain,
    ( X1 = k9_tmap_1(X2,X3)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ r1_funct_2(u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),X1,k7_tmap_1(X2,u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X2))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_40,plain,
    ( r1_funct_2(X1,X2,X3,X4,X5,X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X5,X3,X4)
    | ~ v1_funct_2(X5,X1,X2)
    | ~ v1_funct_1(X5) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( v1_funct_2(k7_tmap_1(X1,u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_27])).

cnf(c_0_42,plain,
    ( m1_subset_1(k7_tmap_1(X1,u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_27])).

fof(c_0_43,plain,(
    ! [X31,X32,X33,X34] :
      ( v2_struct_0(X31)
      | ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
      | v2_struct_0(X33)
      | ~ m1_pre_topc(X33,X31)
      | u1_struct_0(X33) != X32
      | ~ m1_subset_1(X34,u1_struct_0(X33))
      | r1_tmap_1(X33,k6_tmap_1(X31,X32),k2_tmap_1(X31,k6_tmap_1(X31,X32),k7_tmap_1(X31,X32),X33),X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t110_tmap_1])])])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k9_tmap_1(X1,X2) = k7_tmap_1(X1,u1_struct_0(X2))
    | v1_xboole_0(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X3)
    | r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | u1_struct_0(X3) != X2
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r1_tmap_1(esk4_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),esk4_0),esk5_0)
    | ~ v1_funct_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),c_0_48])]),c_0_49])).

cnf(c_0_52,plain,
    ( r1_tmap_1(X1,k8_tmap_1(X2,X3),k2_tmap_1(X2,k8_tmap_1(X2,X3),k7_tmap_1(X2,u1_struct_0(X3)),X1),X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | u1_struct_0(X1) != u1_struct_0(X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_25]),c_0_21])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_54,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_55,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | ~ v1_funct_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_46]),c_0_47]),c_0_53]),c_0_48])]),c_0_49]),c_0_54])).

cnf(c_0_56,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_57,plain,(
    ! [X8] :
      ( v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | ~ v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_58,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_47]),c_0_48])]),c_0_49])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_21]),c_0_46]),c_0_48])])).

fof(c_0_61,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_62,negated_conjecture,
    ( ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_49])).

cnf(c_0_63,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:02:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.46  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.19/0.46  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.46  #
% 0.19/0.46  # Preprocessing time       : 0.029 s
% 0.19/0.46  # Presaturation interreduction done
% 0.19/0.46  
% 0.19/0.46  # Proof found!
% 0.19/0.46  # SZS status Theorem
% 0.19/0.46  # SZS output start CNFRefutation
% 0.19/0.46  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_tmap_1)).
% 0.19/0.46  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.19/0.46  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.19/0.46  fof(d12_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))=>(X3=k9_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X4)),X3,k7_tmap_1(X1,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_tmap_1)).
% 0.19/0.46  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.19/0.46  fof(dt_k7_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 0.19/0.46  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 0.19/0.46  fof(t119_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>r1_tmap_1(X2,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_tmap_1)).
% 0.19/0.46  fof(t110_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(u1_struct_0(X3)=X2=>![X4]:(m1_subset_1(X4,u1_struct_0(X3))=>r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_tmap_1)).
% 0.19/0.46  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.46  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.46  fof(c_0_11, plain, ![X15, X16, X17, X18]:((X17!=k8_tmap_1(X15,X16)|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X15)))|(X18!=u1_struct_0(X16)|X17=k6_tmap_1(X15,X18)))|(~v1_pre_topc(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))|~m1_pre_topc(X16,X15)|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&((m1_subset_1(esk1_3(X15,X16,X17),k1_zfmisc_1(u1_struct_0(X15)))|X17=k8_tmap_1(X15,X16)|(~v1_pre_topc(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))|~m1_pre_topc(X16,X15)|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&((esk1_3(X15,X16,X17)=u1_struct_0(X16)|X17=k8_tmap_1(X15,X16)|(~v1_pre_topc(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))|~m1_pre_topc(X16,X15)|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(X17!=k6_tmap_1(X15,esk1_3(X15,X16,X17))|X17=k8_tmap_1(X15,X16)|(~v1_pre_topc(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))|~m1_pre_topc(X16,X15)|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 0.19/0.46  fof(c_0_12, plain, ![X27, X28]:(((v1_pre_topc(k8_tmap_1(X27,X28))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|~m1_pre_topc(X28,X27)))&(v2_pre_topc(k8_tmap_1(X27,X28))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|~m1_pre_topc(X28,X27))))&(l1_pre_topc(k8_tmap_1(X27,X28))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|~m1_pre_topc(X28,X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.19/0.46  cnf(c_0_13, plain, (X1=k6_tmap_1(X2,X4)|v2_struct_0(X2)|X1!=k8_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.46  cnf(c_0_14, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.46  cnf(c_0_15, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.46  cnf(c_0_16, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.46  fof(c_0_17, plain, ![X35, X36]:(~l1_pre_topc(X35)|(~m1_pre_topc(X36,X35)|m1_subset_1(u1_struct_0(X36),k1_zfmisc_1(u1_struct_0(X35))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.19/0.46  fof(c_0_18, plain, ![X20, X21, X22, X23]:((X22!=k9_tmap_1(X20,X21)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))|(X23!=u1_struct_0(X21)|r1_funct_2(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)),u1_struct_0(X20),u1_struct_0(k6_tmap_1(X20,X23)),X22,k7_tmap_1(X20,X23))))|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21))))))|~m1_pre_topc(X21,X20)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&((m1_subset_1(esk2_3(X20,X21,X22),k1_zfmisc_1(u1_struct_0(X20)))|X22=k9_tmap_1(X20,X21)|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21))))))|~m1_pre_topc(X21,X20)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&((esk2_3(X20,X21,X22)=u1_struct_0(X21)|X22=k9_tmap_1(X20,X21)|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21))))))|~m1_pre_topc(X21,X20)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(~r1_funct_2(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)),u1_struct_0(X20),u1_struct_0(k6_tmap_1(X20,esk2_3(X20,X21,X22))),X22,k7_tmap_1(X20,esk2_3(X20,X21,X22)))|X22=k9_tmap_1(X20,X21)|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21)))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(k8_tmap_1(X20,X21))))))|~m1_pre_topc(X21,X20)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).
% 0.19/0.46  fof(c_0_19, plain, ![X29, X30]:((u1_struct_0(k6_tmap_1(X29,X30))=u1_struct_0(X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))&(u1_pre_topc(k6_tmap_1(X29,X30))=k5_tmap_1(X29,X30)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.19/0.46  cnf(c_0_20, plain, (k8_tmap_1(X1,X2)=k6_tmap_1(X1,X3)|v2_struct_0(X1)|X3!=u1_struct_0(X2)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]), c_0_14]), c_0_15]), c_0_16])).
% 0.19/0.46  cnf(c_0_21, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.46  cnf(c_0_22, plain, (X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,esk2_3(X1,X2,X3))),X3,k7_tmap_1(X1,esk2_3(X1,X2,X3)))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.46  cnf(c_0_23, plain, (esk2_3(X1,X2,X3)=u1_struct_0(X2)|X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.46  cnf(c_0_24, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.46  cnf(c_0_25, plain, (k6_tmap_1(X1,u1_struct_0(X2))=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_20]), c_0_21])).
% 0.19/0.46  cnf(c_0_26, plain, (X1=k9_tmap_1(X2,X3)|v2_struct_0(X2)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~r1_funct_2(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X2,u1_struct_0(X3))),X1,k7_tmap_1(X2,u1_struct_0(X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))|~v1_funct_1(X1)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.46  cnf(c_0_27, plain, (u1_struct_0(k8_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_21])).
% 0.19/0.46  fof(c_0_28, plain, ![X25, X26]:(((v1_funct_1(k7_tmap_1(X25,X26))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))))&(v1_funct_2(k7_tmap_1(X25,X26),u1_struct_0(X25),u1_struct_0(k6_tmap_1(X25,X26)))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25))))))&(m1_subset_1(k7_tmap_1(X25,X26),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(k6_tmap_1(X25,X26)))))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).
% 0.19/0.46  cnf(c_0_29, plain, (X1=k9_tmap_1(X2,X3)|v2_struct_0(X2)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~r1_funct_2(u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X2,u1_struct_0(X3))),X1,k7_tmap_1(X2,u1_struct_0(X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X2))|~v1_funct_1(X1)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.46  fof(c_0_30, plain, ![X9, X10, X11, X12, X13, X14]:((~r1_funct_2(X9,X10,X11,X12,X13,X14)|X13=X14|(v1_xboole_0(X10)|v1_xboole_0(X12)|~v1_funct_1(X13)|~v1_funct_2(X13,X9,X10)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|~v1_funct_1(X14)|~v1_funct_2(X14,X11,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))&(X13!=X14|r1_funct_2(X9,X10,X11,X12,X13,X14)|(v1_xboole_0(X10)|v1_xboole_0(X12)|~v1_funct_1(X13)|~v1_funct_2(X13,X9,X10)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|~v1_funct_1(X14)|~v1_funct_2(X14,X11,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 0.19/0.46  cnf(c_0_31, plain, (v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.46  cnf(c_0_32, plain, (m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.46  fof(c_0_33, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>r1_tmap_1(X2,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X3))))), inference(assume_negation,[status(cth)],[t119_tmap_1])).
% 0.19/0.46  cnf(c_0_34, plain, (X1=k9_tmap_1(X2,X3)|v2_struct_0(X2)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~r1_funct_2(u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)),X1,k7_tmap_1(X2,u1_struct_0(X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X2))|~v1_funct_1(X1)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_29, c_0_25])).
% 0.19/0.46  cnf(c_0_35, plain, (r1_funct_2(X3,X4,X5,X6,X1,X2)|v1_xboole_0(X4)|v1_xboole_0(X6)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X5,X6)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.46  cnf(c_0_36, plain, (v1_funct_2(k7_tmap_1(X1,u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_25]), c_0_21])).
% 0.19/0.46  cnf(c_0_37, plain, (m1_subset_1(k7_tmap_1(X1,u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_25]), c_0_21])).
% 0.19/0.46  fof(c_0_38, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&~r1_tmap_1(esk4_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_33])])])])).
% 0.19/0.46  cnf(c_0_39, plain, (X1=k9_tmap_1(X2,X3)|v2_struct_0(X2)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~r1_funct_2(u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),X1,k7_tmap_1(X2,u1_struct_0(X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X2))|~v1_funct_1(X1)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_34, c_0_27])).
% 0.19/0.46  cnf(c_0_40, plain, (r1_funct_2(X1,X2,X3,X4,X5,X5)|v1_xboole_0(X4)|v1_xboole_0(X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(X5,X3,X4)|~v1_funct_2(X5,X1,X2)|~v1_funct_1(X5)), inference(er,[status(thm)],[c_0_35])).
% 0.19/0.46  cnf(c_0_41, plain, (v1_funct_2(k7_tmap_1(X1,u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(X1))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_36, c_0_27])).
% 0.19/0.46  cnf(c_0_42, plain, (m1_subset_1(k7_tmap_1(X1,u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_37, c_0_27])).
% 0.19/0.46  fof(c_0_43, plain, ![X31, X32, X33, X34]:(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|(v2_struct_0(X33)|~m1_pre_topc(X33,X31)|(u1_struct_0(X33)!=X32|(~m1_subset_1(X34,u1_struct_0(X33))|r1_tmap_1(X33,k6_tmap_1(X31,X32),k2_tmap_1(X31,k6_tmap_1(X31,X32),k7_tmap_1(X31,X32),X33),X34)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t110_tmap_1])])])])).
% 0.19/0.46  cnf(c_0_44, negated_conjecture, (~r1_tmap_1(esk4_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.46  cnf(c_0_45, plain, (k9_tmap_1(X1,X2)=k7_tmap_1(X1,u1_struct_0(X2))|v1_xboole_0(u1_struct_0(X1))|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42])).
% 0.19/0.46  cnf(c_0_46, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.46  cnf(c_0_47, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.46  cnf(c_0_48, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.46  cnf(c_0_49, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.46  cnf(c_0_50, plain, (v2_struct_0(X1)|v2_struct_0(X3)|r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X3,X1)|u1_struct_0(X3)!=X2|~m1_subset_1(X4,u1_struct_0(X3))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.46  cnf(c_0_51, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|~r1_tmap_1(esk4_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),esk4_0),esk5_0)|~v1_funct_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47]), c_0_48])]), c_0_49])).
% 0.19/0.46  cnf(c_0_52, plain, (r1_tmap_1(X1,k8_tmap_1(X2,X3),k2_tmap_1(X2,k8_tmap_1(X2,X3),k7_tmap_1(X2,u1_struct_0(X3)),X1),X4)|v2_struct_0(X2)|v2_struct_0(X1)|u1_struct_0(X1)!=u1_struct_0(X3)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~m1_subset_1(X4,u1_struct_0(X1))|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_25]), c_0_21])).
% 0.19/0.46  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.46  cnf(c_0_54, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.46  cnf(c_0_55, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|~v1_funct_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_46]), c_0_47]), c_0_53]), c_0_48])]), c_0_49]), c_0_54])).
% 0.19/0.46  cnf(c_0_56, plain, (v1_funct_1(k7_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.46  fof(c_0_57, plain, ![X8]:(v2_struct_0(X8)|~l1_struct_0(X8)|~v1_xboole_0(u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.46  cnf(c_0_58, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_47]), c_0_48])]), c_0_49])).
% 0.19/0.46  cnf(c_0_59, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.46  cnf(c_0_60, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_21]), c_0_46]), c_0_48])])).
% 0.19/0.46  fof(c_0_61, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.46  cnf(c_0_62, negated_conjecture, (~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_49])).
% 0.19/0.46  cnf(c_0_63, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.46  cnf(c_0_64, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_48])]), ['proof']).
% 0.19/0.46  # SZS output end CNFRefutation
% 0.19/0.46  # Proof object total steps             : 65
% 0.19/0.46  # Proof object clause steps            : 42
% 0.19/0.46  # Proof object formula steps           : 23
% 0.19/0.46  # Proof object conjectures             : 16
% 0.19/0.46  # Proof object clause conjectures      : 13
% 0.19/0.46  # Proof object formula conjectures     : 3
% 0.19/0.46  # Proof object initial clauses used    : 22
% 0.19/0.46  # Proof object initial formulas used   : 11
% 0.19/0.46  # Proof object generating inferences   : 19
% 0.19/0.46  # Proof object simplifying inferences  : 33
% 0.19/0.46  # Training examples: 0 positive, 0 negative
% 0.19/0.46  # Parsed axioms                        : 11
% 0.19/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.46  # Initial clauses                      : 29
% 0.19/0.46  # Removed in clause preprocessing      : 0
% 0.19/0.46  # Initial clauses in saturation        : 29
% 0.19/0.46  # Processed clauses                    : 379
% 0.19/0.46  # ...of these trivial                  : 0
% 0.19/0.46  # ...subsumed                          : 194
% 0.19/0.46  # ...remaining for further processing  : 185
% 0.19/0.46  # Other redundant clauses eliminated   : 1
% 0.19/0.46  # Clauses deleted for lack of memory   : 0
% 0.19/0.46  # Backward-subsumed                    : 2
% 0.19/0.46  # Backward-rewritten                   : 2
% 0.19/0.46  # Generated clauses                    : 1298
% 0.19/0.46  # ...of the previous two non-trivial   : 1289
% 0.19/0.46  # Contextual simplify-reflections      : 36
% 0.19/0.46  # Paramodulations                      : 1282
% 0.19/0.46  # Factorizations                       : 0
% 0.19/0.46  # Equation resolutions                 : 16
% 0.19/0.46  # Propositional unsat checks           : 0
% 0.19/0.46  #    Propositional check models        : 0
% 0.19/0.46  #    Propositional check unsatisfiable : 0
% 0.19/0.46  #    Propositional clauses             : 0
% 0.19/0.46  #    Propositional clauses after purity: 0
% 0.19/0.46  #    Propositional unsat core size     : 0
% 0.19/0.46  #    Propositional preprocessing time  : 0.000
% 0.19/0.46  #    Propositional encoding time       : 0.000
% 0.19/0.46  #    Propositional solver time         : 0.000
% 0.19/0.46  #    Success case prop preproc time    : 0.000
% 0.19/0.46  #    Success case prop encoding time   : 0.000
% 0.19/0.46  #    Success case prop solver time     : 0.000
% 0.19/0.46  # Current number of processed clauses  : 151
% 0.19/0.46  #    Positive orientable unit clauses  : 5
% 0.19/0.46  #    Positive unorientable unit clauses: 0
% 0.19/0.46  #    Negative unit clauses             : 4
% 0.19/0.46  #    Non-unit-clauses                  : 142
% 0.19/0.46  # Current number of unprocessed clauses: 967
% 0.19/0.46  # ...number of literals in the above   : 14733
% 0.19/0.46  # Current number of archived formulas  : 0
% 0.19/0.46  # Current number of archived clauses   : 33
% 0.19/0.46  # Clause-clause subsumption calls (NU) : 19930
% 0.19/0.46  # Rec. Clause-clause subsumption calls : 874
% 0.19/0.46  # Non-unit clause-clause subsumptions  : 232
% 0.19/0.46  # Unit Clause-clause subsumption calls : 121
% 0.19/0.46  # Rewrite failures with RHS unbound    : 0
% 0.19/0.46  # BW rewrite match attempts            : 1
% 0.19/0.46  # BW rewrite match successes           : 1
% 0.19/0.46  # Condensation attempts                : 0
% 0.19/0.46  # Condensation successes               : 0
% 0.19/0.46  # Termbank termtop insertions          : 63327
% 0.19/0.46  
% 0.19/0.46  # -------------------------------------------------
% 0.19/0.46  # User time                : 0.118 s
% 0.19/0.46  # System time              : 0.008 s
% 0.19/0.46  # Total time               : 0.126 s
% 0.19/0.46  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
