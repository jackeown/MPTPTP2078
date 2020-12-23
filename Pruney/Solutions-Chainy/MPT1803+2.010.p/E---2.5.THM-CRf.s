%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:27 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 (3080 expanded)
%              Number of clauses        :   71 (1043 expanded)
%              Number of leaves         :   16 ( 795 expanded)
%              Depth                    :   23
%              Number of atoms          :  576 (19839 expanded)
%              Number of equality atoms :   56 (1059 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_tmap_1)).

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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t118_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r1_tsep_1(X2,X3)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X3))
                   => r1_tmap_1(X3,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_tmap_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d3_tsep_1,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ( r1_tsep_1(X1,X2)
          <=> r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_16,plain,(
    ! [X47,X48] :
      ( ( u1_struct_0(k6_tmap_1(X47,X48)) = u1_struct_0(X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47) )
      & ( u1_pre_topc(k6_tmap_1(X47,X48)) = k5_tmap_1(X47,X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

fof(c_0_17,plain,(
    ! [X57,X58] :
      ( ~ l1_pre_topc(X57)
      | ~ m1_pre_topc(X58,X57)
      | m1_subset_1(u1_struct_0(X58),k1_zfmisc_1(u1_struct_0(X57))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_18,negated_conjecture,(
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

fof(c_0_19,plain,(
    ! [X29,X30,X31,X32] :
      ( ( X31 != k8_tmap_1(X29,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X29)))
        | X32 != u1_struct_0(X30)
        | X31 = k6_tmap_1(X29,X32)
        | ~ v1_pre_topc(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( m1_subset_1(esk3_3(X29,X30,X31),k1_zfmisc_1(u1_struct_0(X29)))
        | X31 = k8_tmap_1(X29,X30)
        | ~ v1_pre_topc(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( esk3_3(X29,X30,X31) = u1_struct_0(X30)
        | X31 = k8_tmap_1(X29,X30)
        | ~ v1_pre_topc(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( X31 != k6_tmap_1(X29,esk3_3(X29,X30,X31))
        | X31 = k8_tmap_1(X29,X30)
        | ~ v1_pre_topc(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_20,plain,(
    ! [X43,X44] :
      ( ( v1_pre_topc(k8_tmap_1(X43,X44))
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43)
        | ~ m1_pre_topc(X44,X43) )
      & ( v2_pre_topc(k8_tmap_1(X43,X44))
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43)
        | ~ m1_pre_topc(X44,X43) )
      & ( l1_pre_topc(k8_tmap_1(X43,X44))
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43)
        | ~ m1_pre_topc(X44,X43) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

cnf(c_0_21,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & ~ v2_struct_0(esk6_0)
    & m1_pre_topc(esk6_0,esk5_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk6_0))
    & ~ r1_tmap_1(esk6_0,k8_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k8_tmap_1(esk5_0,esk6_0),k9_tmap_1(esk5_0,esk6_0),esk6_0),esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

cnf(c_0_24,plain,
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

cnf(c_0_25,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k6_tmap_1(X1,u1_struct_0(X2)) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])]),c_0_22]),c_0_25]),c_0_26]),c_0_27])).

fof(c_0_34,plain,(
    ! [X41,X42] :
      ( ( v1_funct_1(k7_tmap_1(X41,X42))
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41))) )
      & ( v1_funct_2(k7_tmap_1(X41,X42),u1_struct_0(X41),u1_struct_0(k6_tmap_1(X41,X42)))
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41))) )
      & ( m1_subset_1(k7_tmap_1(X41,X42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(k6_tmap_1(X41,X42)))))
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

fof(c_0_35,plain,(
    ! [X34,X35,X36,X37] :
      ( ( X36 != k9_tmap_1(X34,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X34)))
        | X37 != u1_struct_0(X35)
        | r1_funct_2(u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35)),u1_struct_0(X34),u1_struct_0(k6_tmap_1(X34,X37)),X36,k7_tmap_1(X34,X37))
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35)))
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35)))))
        | ~ m1_pre_topc(X35,X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( m1_subset_1(esk4_3(X34,X35,X36),k1_zfmisc_1(u1_struct_0(X34)))
        | X36 = k9_tmap_1(X34,X35)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35)))
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35)))))
        | ~ m1_pre_topc(X35,X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( esk4_3(X34,X35,X36) = u1_struct_0(X35)
        | X36 = k9_tmap_1(X34,X35)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35)))
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35)))))
        | ~ m1_pre_topc(X35,X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( ~ r1_funct_2(u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35)),u1_struct_0(X34),u1_struct_0(k6_tmap_1(X34,esk4_3(X34,X35,X36))),X36,k7_tmap_1(X34,esk4_3(X34,X35,X36)))
        | X36 = k9_tmap_1(X34,X35)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35)))
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35)))))
        | ~ m1_pre_topc(X35,X34)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).

cnf(c_0_36,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk5_0,u1_struct_0(esk6_0))) = u1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( k6_tmap_1(esk5_0,u1_struct_0(esk6_0)) = k8_tmap_1(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_38,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk5_0,esk6_0)) = u1_struct_0(esk5_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_22])).

cnf(c_0_43,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( esk4_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( X1 = k9_tmap_1(esk5_0,esk6_0)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v1_funct_2(X1,u1_struct_0(esk5_0),u1_struct_0(esk5_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_30]),c_0_29]),c_0_31])]),c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))))
    | ~ m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_37]),c_0_40]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk5_0,u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),u1_struct_0(esk5_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_37]),c_0_40]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_49,negated_conjecture,
    ( esk4_3(esk5_0,esk6_0,X1) = u1_struct_0(esk6_0)
    | X1 = k9_tmap_1(esk5_0,esk6_0)
    | ~ v1_funct_2(X1,u1_struct_0(esk5_0),u1_struct_0(esk5_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_40]),c_0_30]),c_0_29]),c_0_31])]),c_0_32])).

fof(c_0_50,plain,(
    ! [X49,X50,X51,X52] :
      ( v2_struct_0(X49)
      | ~ v2_pre_topc(X49)
      | ~ l1_pre_topc(X49)
      | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
      | v2_struct_0(X51)
      | ~ m1_pre_topc(X51,X49)
      | u1_struct_0(X51) != X50
      | ~ m1_subset_1(X52,u1_struct_0(X51))
      | r1_tmap_1(X51,k6_tmap_1(X49,X50),k2_tmap_1(X49,k6_tmap_1(X49,X50),k7_tmap_1(X49,X50),X51),X52) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t110_tmap_1])])])])).

cnf(c_0_51,negated_conjecture,
    ( k7_tmap_1(esk5_0,u1_struct_0(esk6_0)) = k9_tmap_1(esk5_0,esk6_0)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,k7_tmap_1(esk5_0,u1_struct_0(esk6_0))),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( esk4_3(esk5_0,esk6_0,k7_tmap_1(esk5_0,u1_struct_0(esk6_0))) = u1_struct_0(esk6_0)
    | k7_tmap_1(esk5_0,u1_struct_0(esk6_0)) = k9_tmap_1(esk5_0,esk6_0)
    | ~ m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X3)
    | r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | u1_struct_0(X3) != X2
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( k7_tmap_1(esk5_0,u1_struct_0(esk6_0)) = k9_tmap_1(esk5_0,esk6_0)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,k7_tmap_1(esk5_0,u1_struct_0(esk6_0))),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_22]),c_0_29]),c_0_31])])).

cnf(c_0_55,negated_conjecture,
    ( esk4_3(esk5_0,esk6_0,k7_tmap_1(esk5_0,u1_struct_0(esk6_0))) = u1_struct_0(esk6_0)
    | k7_tmap_1(esk5_0,u1_struct_0(esk6_0)) = k9_tmap_1(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_22]),c_0_29]),c_0_31])])).

cnf(c_0_56,plain,
    ( r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(X1)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(X1)),k7_tmap_1(X2,u1_struct_0(X1)),X1),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_53]),c_0_22])).

cnf(c_0_57,negated_conjecture,
    ( k7_tmap_1(esk5_0,u1_struct_0(esk6_0)) = k9_tmap_1(esk5_0,esk6_0)
    | m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_59,negated_conjecture,
    ( r1_tmap_1(esk6_0,k8_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k8_tmap_1(esk5_0,esk6_0),k9_tmap_1(esk5_0,esk6_0),esk6_0),X1)
    | m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_37]),c_0_37]),c_0_30]),c_0_29]),c_0_31])]),c_0_32]),c_0_58])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tmap_1(esk6_0,k8_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k8_tmap_1(esk5_0,esk6_0),k9_tmap_1(esk5_0,esk6_0),esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_62,plain,(
    ! [X45,X46] :
      ( ( v1_funct_1(k9_tmap_1(X45,X46))
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45)
        | ~ m1_pre_topc(X46,X45) )
      & ( v1_funct_2(k9_tmap_1(X45,X46),u1_struct_0(X45),u1_struct_0(k8_tmap_1(X45,X46)))
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45)
        | ~ m1_pre_topc(X46,X45) )
      & ( m1_subset_1(k9_tmap_1(X45,X46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(k8_tmap_1(X45,X46)))))
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45)
        | ~ m1_pre_topc(X46,X45) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

fof(c_0_63,plain,(
    ! [X23,X24,X25,X26,X27,X28] :
      ( ( ~ r1_funct_2(X23,X24,X25,X26,X27,X28)
        | X27 = X28
        | v1_xboole_0(X24)
        | v1_xboole_0(X26)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X23,X24)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X25,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( X27 != X28
        | r1_funct_2(X23,X24,X25,X26,X27,X28)
        | v1_xboole_0(X24)
        | v1_xboole_0(X26)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X23,X24)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X25,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_65,plain,
    ( r1_funct_2(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X2,X4)),X1,k7_tmap_1(X2,X4))
    | v2_struct_0(X2)
    | X1 != k9_tmap_1(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != u1_struct_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))))
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_66,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_67,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_64])])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),u1_struct_0(esk5_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_64])])).

cnf(c_0_72,plain,
    ( v2_struct_0(X1)
    | r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))),k9_tmap_1(X1,X2),k7_tmap_1(X1,u1_struct_0(X2)))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_65])]),c_0_22]),c_0_66]),c_0_67]),c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_74,negated_conjecture,
    ( X1 = k7_tmap_1(esk5_0,u1_struct_0(esk6_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(X2)
    | ~ r1_funct_2(X3,X2,u1_struct_0(esk5_0),u1_struct_0(esk5_0),X1,k7_tmap_1(esk5_0,u1_struct_0(esk6_0)))
    | ~ v1_funct_2(X1,X3,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_47])])).

cnf(c_0_75,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),k9_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_29]),c_0_40]),c_0_37]),c_0_40]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_76,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_73,c_0_40])).

cnf(c_0_77,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_29]),c_0_40]),c_0_30]),c_0_31])]),c_0_32])).

fof(c_0_79,plain,(
    ! [X17,X18,X19] :
      ( ~ r2_hidden(X17,X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X19))
      | ~ v1_xboole_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_80,negated_conjecture,
    ( k7_tmap_1(esk5_0,u1_struct_0(esk6_0)) = k9_tmap_1(esk5_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76]),c_0_77]),c_0_78])])).

cnf(c_0_81,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( r1_tmap_1(esk6_0,k8_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k8_tmap_1(esk5_0,esk6_0),k9_tmap_1(esk5_0,esk6_0),esk6_0),X1)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_80]),c_0_37]),c_0_37]),c_0_30]),c_0_29]),c_0_31])]),c_0_32]),c_0_58])).

fof(c_0_83,plain,(
    ! [X53,X54,X55,X56] :
      ( v2_struct_0(X53)
      | ~ v2_pre_topc(X53)
      | ~ l1_pre_topc(X53)
      | v2_struct_0(X54)
      | ~ m1_pre_topc(X54,X53)
      | v2_struct_0(X55)
      | ~ m1_pre_topc(X55,X53)
      | ~ r1_tsep_1(X54,X55)
      | ~ m1_subset_1(X56,u1_struct_0(X55))
      | r1_tmap_1(X55,k8_tmap_1(X53,X54),k2_tmap_1(X53,k8_tmap_1(X53,X54),k9_tmap_1(X53,X54),X55),X56) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t118_tmap_1])])])])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_hidden(X1,u1_struct_0(esk6_0))
    | ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_64])).

cnf(c_0_85,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_60]),c_0_61])).

fof(c_0_86,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_xboole_0(X11,X12) )
      & ( r2_hidden(esk2_2(X11,X12),X12)
        | r1_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_87,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | r1_tmap_1(X3,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

fof(c_0_88,plain,(
    ! [X39,X40] :
      ( ( ~ r1_tsep_1(X39,X40)
        | r1_xboole_0(u1_struct_0(X39),u1_struct_0(X40))
        | ~ l1_struct_0(X40)
        | ~ l1_struct_0(X39) )
      & ( ~ r1_xboole_0(u1_struct_0(X39),u1_struct_0(X40))
        | r1_tsep_1(X39,X40)
        | ~ l1_struct_0(X40)
        | ~ l1_struct_0(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).

cnf(c_0_89,negated_conjecture,
    ( ~ r2_hidden(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85])])).

cnf(c_0_90,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

fof(c_0_91,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_pre_topc(X22,X21)
      | l1_pre_topc(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_92,negated_conjecture,
    ( r1_tmap_1(esk6_0,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),esk6_0),esk7_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X2,esk6_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk6_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_60]),c_0_58])).

cnf(c_0_93,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( r1_xboole_0(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

fof(c_0_95,plain,(
    ! [X20] :
      ( ~ l1_pre_topc(X20)
      | l1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_96,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( r1_tmap_1(esk6_0,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),esk6_0),esk7_0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk6_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_struct_0(esk6_0)
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])])).

cnf(c_0_98,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_29]),c_0_31])])).

cnf(c_0_100,negated_conjecture,
    ( r1_tmap_1(esk6_0,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),esk6_0),esk7_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk6_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99])])).

cnf(c_0_101,negated_conjecture,
    ( r1_tmap_1(esk6_0,k8_tmap_1(esk5_0,X1),k2_tmap_1(esk5_0,k8_tmap_1(esk5_0,X1),k9_tmap_1(esk5_0,X1),esk6_0),esk7_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_102,negated_conjecture,
    ( ~ l1_struct_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_29]),c_0_61]),c_0_58])).

cnf(c_0_103,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_98]),c_0_99])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:08:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.46  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05AN
% 0.20/0.46  # and selection function PSelectComplexExceptUniqMaxPosHorn.
% 0.20/0.46  #
% 0.20/0.46  # Preprocessing time       : 0.031 s
% 0.20/0.46  # Presaturation interreduction done
% 0.20/0.46  
% 0.20/0.46  # Proof found!
% 0.20/0.46  # SZS status Theorem
% 0.20/0.46  # SZS output start CNFRefutation
% 0.20/0.46  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.20/0.46  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.20/0.46  fof(t119_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>r1_tmap_1(X2,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_tmap_1)).
% 0.20/0.46  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_tmap_1)).
% 0.20/0.46  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.20/0.46  fof(dt_k7_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 0.20/0.46  fof(d12_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))=>(X3=k9_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X4)),X3,k7_tmap_1(X1,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_tmap_1)).
% 0.20/0.46  fof(t110_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(u1_struct_0(X3)=X2=>![X4]:(m1_subset_1(X4,u1_struct_0(X3))=>r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_tmap_1)).
% 0.20/0.46  fof(dt_k9_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_tmap_1)).
% 0.20/0.46  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 0.20/0.46  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.20/0.46  fof(t118_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(r1_tsep_1(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X3))=>r1_tmap_1(X3,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_tmap_1)).
% 0.20/0.46  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.46  fof(d3_tsep_1, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>(r1_tsep_1(X1,X2)<=>r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 0.20/0.46  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.46  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.46  fof(c_0_16, plain, ![X47, X48]:((u1_struct_0(k6_tmap_1(X47,X48))=u1_struct_0(X47)|~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47)))&(u1_pre_topc(k6_tmap_1(X47,X48))=k5_tmap_1(X47,X48)|~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.20/0.46  fof(c_0_17, plain, ![X57, X58]:(~l1_pre_topc(X57)|(~m1_pre_topc(X58,X57)|m1_subset_1(u1_struct_0(X58),k1_zfmisc_1(u1_struct_0(X57))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.20/0.46  fof(c_0_18, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>r1_tmap_1(X2,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X3))))), inference(assume_negation,[status(cth)],[t119_tmap_1])).
% 0.20/0.46  fof(c_0_19, plain, ![X29, X30, X31, X32]:((X31!=k8_tmap_1(X29,X30)|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X29)))|(X32!=u1_struct_0(X30)|X31=k6_tmap_1(X29,X32)))|(~v1_pre_topc(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31))|~m1_pre_topc(X30,X29)|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))&((m1_subset_1(esk3_3(X29,X30,X31),k1_zfmisc_1(u1_struct_0(X29)))|X31=k8_tmap_1(X29,X30)|(~v1_pre_topc(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31))|~m1_pre_topc(X30,X29)|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))&((esk3_3(X29,X30,X31)=u1_struct_0(X30)|X31=k8_tmap_1(X29,X30)|(~v1_pre_topc(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31))|~m1_pre_topc(X30,X29)|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))&(X31!=k6_tmap_1(X29,esk3_3(X29,X30,X31))|X31=k8_tmap_1(X29,X30)|(~v1_pre_topc(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31))|~m1_pre_topc(X30,X29)|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 0.20/0.46  fof(c_0_20, plain, ![X43, X44]:(((v1_pre_topc(k8_tmap_1(X43,X44))|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)|~m1_pre_topc(X44,X43)))&(v2_pre_topc(k8_tmap_1(X43,X44))|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)|~m1_pre_topc(X44,X43))))&(l1_pre_topc(k8_tmap_1(X43,X44))|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)|~m1_pre_topc(X44,X43)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.20/0.46  cnf(c_0_21, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.46  cnf(c_0_22, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.46  fof(c_0_23, negated_conjecture, (((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&((~v2_struct_0(esk6_0)&m1_pre_topc(esk6_0,esk5_0))&(m1_subset_1(esk7_0,u1_struct_0(esk6_0))&~r1_tmap_1(esk6_0,k8_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k8_tmap_1(esk5_0,esk6_0),k9_tmap_1(esk5_0,esk6_0),esk6_0),esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 0.20/0.46  cnf(c_0_24, plain, (X1=k6_tmap_1(X2,X4)|v2_struct_0(X2)|X1!=k8_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.46  cnf(c_0_25, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.46  cnf(c_0_26, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.46  cnf(c_0_27, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.46  cnf(c_0_28, plain, (u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2)))=u1_struct_0(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.46  cnf(c_0_29, negated_conjecture, (m1_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.46  cnf(c_0_30, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.46  cnf(c_0_31, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.46  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.46  cnf(c_0_33, plain, (k6_tmap_1(X1,u1_struct_0(X2))=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])]), c_0_22]), c_0_25]), c_0_26]), c_0_27])).
% 0.20/0.46  fof(c_0_34, plain, ![X41, X42]:(((v1_funct_1(k7_tmap_1(X41,X42))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))))&(v1_funct_2(k7_tmap_1(X41,X42),u1_struct_0(X41),u1_struct_0(k6_tmap_1(X41,X42)))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41))))))&(m1_subset_1(k7_tmap_1(X41,X42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(k6_tmap_1(X41,X42)))))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).
% 0.20/0.46  fof(c_0_35, plain, ![X34, X35, X36, X37]:((X36!=k9_tmap_1(X34,X35)|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X34)))|(X37!=u1_struct_0(X35)|r1_funct_2(u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35)),u1_struct_0(X34),u1_struct_0(k6_tmap_1(X34,X37)),X36,k7_tmap_1(X34,X37))))|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35)))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35))))))|~m1_pre_topc(X35,X34)|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)))&((m1_subset_1(esk4_3(X34,X35,X36),k1_zfmisc_1(u1_struct_0(X34)))|X36=k9_tmap_1(X34,X35)|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35)))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35))))))|~m1_pre_topc(X35,X34)|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)))&((esk4_3(X34,X35,X36)=u1_struct_0(X35)|X36=k9_tmap_1(X34,X35)|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35)))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35))))))|~m1_pre_topc(X35,X34)|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)))&(~r1_funct_2(u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35)),u1_struct_0(X34),u1_struct_0(k6_tmap_1(X34,esk4_3(X34,X35,X36))),X36,k7_tmap_1(X34,esk4_3(X34,X35,X36)))|X36=k9_tmap_1(X34,X35)|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35)))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(k8_tmap_1(X34,X35))))))|~m1_pre_topc(X35,X34)|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).
% 0.20/0.46  cnf(c_0_36, negated_conjecture, (u1_struct_0(k6_tmap_1(esk5_0,u1_struct_0(esk6_0)))=u1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])]), c_0_32])).
% 0.20/0.46  cnf(c_0_37, negated_conjecture, (k6_tmap_1(esk5_0,u1_struct_0(esk6_0))=k8_tmap_1(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_29]), c_0_30]), c_0_31])]), c_0_32])).
% 0.20/0.46  cnf(c_0_38, plain, (v1_funct_1(k7_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.46  cnf(c_0_39, plain, (m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.46  cnf(c_0_40, negated_conjecture, (u1_struct_0(k8_tmap_1(esk5_0,esk6_0))=u1_struct_0(esk5_0)), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.46  cnf(c_0_41, plain, (m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.46  cnf(c_0_42, plain, (v2_struct_0(X1)|v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_38, c_0_22])).
% 0.20/0.46  cnf(c_0_43, plain, (v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.46  cnf(c_0_44, plain, (esk4_3(X1,X2,X3)=u1_struct_0(X2)|X3=k9_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.46  cnf(c_0_45, negated_conjecture, (X1=k9_tmap_1(esk5_0,esk6_0)|m1_subset_1(esk4_3(esk5_0,esk6_0,X1),k1_zfmisc_1(u1_struct_0(esk5_0)))|~v1_funct_2(X1,u1_struct_0(esk5_0),u1_struct_0(esk5_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_30]), c_0_29]), c_0_31])]), c_0_32])).
% 0.20/0.46  cnf(c_0_46, negated_conjecture, (m1_subset_1(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))))|~m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_37]), c_0_40]), c_0_30]), c_0_31])]), c_0_32])).
% 0.20/0.46  cnf(c_0_47, negated_conjecture, (v1_funct_1(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_29]), c_0_30]), c_0_31])]), c_0_32])).
% 0.20/0.46  cnf(c_0_48, negated_conjecture, (v1_funct_2(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),u1_struct_0(esk5_0),u1_struct_0(esk5_0))|~m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_37]), c_0_40]), c_0_30]), c_0_31])]), c_0_32])).
% 0.20/0.46  cnf(c_0_49, negated_conjecture, (esk4_3(esk5_0,esk6_0,X1)=u1_struct_0(esk6_0)|X1=k9_tmap_1(esk5_0,esk6_0)|~v1_funct_2(X1,u1_struct_0(esk5_0),u1_struct_0(esk5_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_40]), c_0_30]), c_0_29]), c_0_31])]), c_0_32])).
% 0.20/0.46  fof(c_0_50, plain, ![X49, X50, X51, X52]:(v2_struct_0(X49)|~v2_pre_topc(X49)|~l1_pre_topc(X49)|(~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))|(v2_struct_0(X51)|~m1_pre_topc(X51,X49)|(u1_struct_0(X51)!=X50|(~m1_subset_1(X52,u1_struct_0(X51))|r1_tmap_1(X51,k6_tmap_1(X49,X50),k2_tmap_1(X49,k6_tmap_1(X49,X50),k7_tmap_1(X49,X50),X51),X52)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t110_tmap_1])])])])).
% 0.20/0.46  cnf(c_0_51, negated_conjecture, (k7_tmap_1(esk5_0,u1_struct_0(esk6_0))=k9_tmap_1(esk5_0,esk6_0)|m1_subset_1(esk4_3(esk5_0,esk6_0,k7_tmap_1(esk5_0,u1_struct_0(esk6_0))),k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])]), c_0_48])).
% 0.20/0.46  cnf(c_0_52, negated_conjecture, (esk4_3(esk5_0,esk6_0,k7_tmap_1(esk5_0,u1_struct_0(esk6_0)))=u1_struct_0(esk6_0)|k7_tmap_1(esk5_0,u1_struct_0(esk6_0))=k9_tmap_1(esk5_0,esk6_0)|~m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_46]), c_0_47])]), c_0_48])).
% 0.20/0.46  cnf(c_0_53, plain, (v2_struct_0(X1)|v2_struct_0(X3)|r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X3,X1)|u1_struct_0(X3)!=X2|~m1_subset_1(X4,u1_struct_0(X3))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.46  cnf(c_0_54, negated_conjecture, (k7_tmap_1(esk5_0,u1_struct_0(esk6_0))=k9_tmap_1(esk5_0,esk6_0)|m1_subset_1(esk4_3(esk5_0,esk6_0,k7_tmap_1(esk5_0,u1_struct_0(esk6_0))),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_22]), c_0_29]), c_0_31])])).
% 0.20/0.46  cnf(c_0_55, negated_conjecture, (esk4_3(esk5_0,esk6_0,k7_tmap_1(esk5_0,u1_struct_0(esk6_0)))=u1_struct_0(esk6_0)|k7_tmap_1(esk5_0,u1_struct_0(esk6_0))=k9_tmap_1(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_22]), c_0_29]), c_0_31])])).
% 0.20/0.46  cnf(c_0_56, plain, (r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(X1)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(X1)),k7_tmap_1(X2,u1_struct_0(X1)),X1),X3)|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_53]), c_0_22])).
% 0.20/0.46  cnf(c_0_57, negated_conjecture, (k7_tmap_1(esk5_0,u1_struct_0(esk6_0))=k9_tmap_1(esk5_0,esk6_0)|m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.46  cnf(c_0_58, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.46  cnf(c_0_59, negated_conjecture, (r1_tmap_1(esk6_0,k8_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k8_tmap_1(esk5_0,esk6_0),k9_tmap_1(esk5_0,esk6_0),esk6_0),X1)|m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_37]), c_0_37]), c_0_30]), c_0_29]), c_0_31])]), c_0_32]), c_0_58])).
% 0.20/0.46  cnf(c_0_60, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.46  cnf(c_0_61, negated_conjecture, (~r1_tmap_1(esk6_0,k8_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k8_tmap_1(esk5_0,esk6_0),k9_tmap_1(esk5_0,esk6_0),esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.46  fof(c_0_62, plain, ![X45, X46]:(((v1_funct_1(k9_tmap_1(X45,X46))|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)|~m1_pre_topc(X46,X45)))&(v1_funct_2(k9_tmap_1(X45,X46),u1_struct_0(X45),u1_struct_0(k8_tmap_1(X45,X46)))|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)|~m1_pre_topc(X46,X45))))&(m1_subset_1(k9_tmap_1(X45,X46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(k8_tmap_1(X45,X46)))))|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)|~m1_pre_topc(X46,X45)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).
% 0.20/0.46  fof(c_0_63, plain, ![X23, X24, X25, X26, X27, X28]:((~r1_funct_2(X23,X24,X25,X26,X27,X28)|X27=X28|(v1_xboole_0(X24)|v1_xboole_0(X26)|~v1_funct_1(X27)|~v1_funct_2(X27,X23,X24)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|~v1_funct_1(X28)|~v1_funct_2(X28,X25,X26)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))))&(X27!=X28|r1_funct_2(X23,X24,X25,X26,X27,X28)|(v1_xboole_0(X24)|v1_xboole_0(X26)|~v1_funct_1(X27)|~v1_funct_2(X27,X23,X24)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|~v1_funct_1(X28)|~v1_funct_2(X28,X25,X26)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 0.20/0.46  cnf(c_0_64, negated_conjecture, (m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 0.20/0.46  cnf(c_0_65, plain, (r1_funct_2(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X2,X4)),X1,k7_tmap_1(X2,X4))|v2_struct_0(X2)|X1!=k9_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X2,X3)))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.46  cnf(c_0_66, plain, (m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.46  cnf(c_0_67, plain, (v1_funct_1(k9_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.46  cnf(c_0_68, plain, (v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.46  cnf(c_0_69, plain, (X5=X6|v1_xboole_0(X2)|v1_xboole_0(X4)|~r1_funct_2(X1,X2,X3,X4,X5,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,X1,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.46  cnf(c_0_70, negated_conjecture, (m1_subset_1(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_64])])).
% 0.20/0.46  cnf(c_0_71, negated_conjecture, (v1_funct_2(k7_tmap_1(esk5_0,u1_struct_0(esk6_0)),u1_struct_0(esk5_0),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_64])])).
% 0.20/0.46  cnf(c_0_72, plain, (v2_struct_0(X1)|r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))),k9_tmap_1(X1,X2),k7_tmap_1(X1,u1_struct_0(X2)))|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_65])]), c_0_22]), c_0_66]), c_0_67]), c_0_68])).
% 0.20/0.46  cnf(c_0_73, negated_conjecture, (v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k8_tmap_1(esk5_0,esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_29]), c_0_30]), c_0_31])]), c_0_32])).
% 0.20/0.46  cnf(c_0_74, negated_conjecture, (X1=k7_tmap_1(esk5_0,u1_struct_0(esk6_0))|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(X2)|~r1_funct_2(X3,X2,u1_struct_0(esk5_0),u1_struct_0(esk5_0),X1,k7_tmap_1(esk5_0,u1_struct_0(esk6_0)))|~v1_funct_2(X1,X3,X2)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_47])])).
% 0.20/0.46  cnf(c_0_75, negated_conjecture, (r1_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),k9_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,u1_struct_0(esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_29]), c_0_40]), c_0_37]), c_0_40]), c_0_30]), c_0_31])]), c_0_32])).
% 0.20/0.46  cnf(c_0_76, negated_conjecture, (v1_funct_2(k9_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0))), inference(rw,[status(thm)],[c_0_73, c_0_40])).
% 0.20/0.46  cnf(c_0_77, negated_conjecture, (v1_funct_1(k9_tmap_1(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_29]), c_0_30]), c_0_31])]), c_0_32])).
% 0.20/0.46  cnf(c_0_78, negated_conjecture, (m1_subset_1(k9_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_29]), c_0_40]), c_0_30]), c_0_31])]), c_0_32])).
% 0.20/0.46  fof(c_0_79, plain, ![X17, X18, X19]:(~r2_hidden(X17,X18)|~m1_subset_1(X18,k1_zfmisc_1(X19))|~v1_xboole_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.20/0.46  cnf(c_0_80, negated_conjecture, (k7_tmap_1(esk5_0,u1_struct_0(esk6_0))=k9_tmap_1(esk5_0,esk6_0)|v1_xboole_0(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76]), c_0_77]), c_0_78])])).
% 0.20/0.46  cnf(c_0_81, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.20/0.46  cnf(c_0_82, negated_conjecture, (r1_tmap_1(esk6_0,k8_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k8_tmap_1(esk5_0,esk6_0),k9_tmap_1(esk5_0,esk6_0),esk6_0),X1)|v1_xboole_0(u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_80]), c_0_37]), c_0_37]), c_0_30]), c_0_29]), c_0_31])]), c_0_32]), c_0_58])).
% 0.20/0.46  fof(c_0_83, plain, ![X53, X54, X55, X56]:(v2_struct_0(X53)|~v2_pre_topc(X53)|~l1_pre_topc(X53)|(v2_struct_0(X54)|~m1_pre_topc(X54,X53)|(v2_struct_0(X55)|~m1_pre_topc(X55,X53)|(~r1_tsep_1(X54,X55)|(~m1_subset_1(X56,u1_struct_0(X55))|r1_tmap_1(X55,k8_tmap_1(X53,X54),k2_tmap_1(X53,k8_tmap_1(X53,X54),k9_tmap_1(X53,X54),X55),X56)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t118_tmap_1])])])])).
% 0.20/0.46  cnf(c_0_84, negated_conjecture, (~r2_hidden(X1,u1_struct_0(esk6_0))|~v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_81, c_0_64])).
% 0.20/0.46  cnf(c_0_85, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_60]), c_0_61])).
% 0.20/0.46  fof(c_0_86, plain, ![X11, X12, X14, X15, X16]:(((r2_hidden(esk2_2(X11,X12),X11)|r1_xboole_0(X11,X12))&(r2_hidden(esk2_2(X11,X12),X12)|r1_xboole_0(X11,X12)))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|~r1_xboole_0(X14,X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.46  cnf(c_0_87, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|r1_tmap_1(X3,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X3),X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)|~r1_tsep_1(X2,X3)|~m1_subset_1(X4,u1_struct_0(X3))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.20/0.46  fof(c_0_88, plain, ![X39, X40]:((~r1_tsep_1(X39,X40)|r1_xboole_0(u1_struct_0(X39),u1_struct_0(X40))|~l1_struct_0(X40)|~l1_struct_0(X39))&(~r1_xboole_0(u1_struct_0(X39),u1_struct_0(X40))|r1_tsep_1(X39,X40)|~l1_struct_0(X40)|~l1_struct_0(X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).
% 0.20/0.46  cnf(c_0_89, negated_conjecture, (~r2_hidden(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85])])).
% 0.20/0.46  cnf(c_0_90, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.20/0.46  fof(c_0_91, plain, ![X21, X22]:(~l1_pre_topc(X21)|(~m1_pre_topc(X22,X21)|l1_pre_topc(X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.46  cnf(c_0_92, negated_conjecture, (r1_tmap_1(esk6_0,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),esk6_0),esk7_0)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(X2,esk6_0)|~v2_pre_topc(X1)|~m1_pre_topc(esk6_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_60]), c_0_58])).
% 0.20/0.46  cnf(c_0_93, plain, (r1_tsep_1(X1,X2)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.20/0.46  cnf(c_0_94, negated_conjecture, (r1_xboole_0(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.20/0.46  fof(c_0_95, plain, ![X20]:(~l1_pre_topc(X20)|l1_struct_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.46  cnf(c_0_96, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.20/0.46  cnf(c_0_97, negated_conjecture, (r1_tmap_1(esk6_0,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),esk6_0),esk7_0)|v2_struct_0(X2)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(esk6_0,X1)|~m1_pre_topc(X2,X1)|~l1_struct_0(esk6_0)|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94])])).
% 0.20/0.46  cnf(c_0_98, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.20/0.46  cnf(c_0_99, negated_conjecture, (l1_pre_topc(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_29]), c_0_31])])).
% 0.20/0.46  cnf(c_0_100, negated_conjecture, (r1_tmap_1(esk6_0,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),esk6_0),esk7_0)|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~m1_pre_topc(esk6_0,X1)|~m1_pre_topc(X2,X1)|~l1_struct_0(X2)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99])])).
% 0.20/0.46  cnf(c_0_101, negated_conjecture, (r1_tmap_1(esk6_0,k8_tmap_1(esk5_0,X1),k2_tmap_1(esk5_0,k8_tmap_1(esk5_0,X1),k9_tmap_1(esk5_0,X1),esk6_0),esk7_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk5_0)|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_29]), c_0_30]), c_0_31])]), c_0_32])).
% 0.20/0.46  cnf(c_0_102, negated_conjecture, (~l1_struct_0(esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_29]), c_0_61]), c_0_58])).
% 0.20/0.46  cnf(c_0_103, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_98]), c_0_99])]), ['proof']).
% 0.20/0.46  # SZS output end CNFRefutation
% 0.20/0.46  # Proof object total steps             : 104
% 0.20/0.46  # Proof object clause steps            : 71
% 0.20/0.46  # Proof object formula steps           : 33
% 0.20/0.46  # Proof object conjectures             : 46
% 0.20/0.46  # Proof object clause conjectures      : 43
% 0.20/0.46  # Proof object formula conjectures     : 3
% 0.20/0.46  # Proof object initial clauses used    : 30
% 0.20/0.46  # Proof object initial formulas used   : 16
% 0.20/0.46  # Proof object generating inferences   : 33
% 0.20/0.46  # Proof object simplifying inferences  : 126
% 0.20/0.46  # Training examples: 0 positive, 0 negative
% 0.20/0.46  # Parsed axioms                        : 17
% 0.20/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.46  # Initial clauses                      : 41
% 0.20/0.46  # Removed in clause preprocessing      : 0
% 0.20/0.46  # Initial clauses in saturation        : 41
% 0.20/0.46  # Processed clauses                    : 638
% 0.20/0.46  # ...of these trivial                  : 11
% 0.20/0.46  # ...subsumed                          : 195
% 0.20/0.46  # ...remaining for further processing  : 432
% 0.20/0.46  # Other redundant clauses eliminated   : 6
% 0.20/0.46  # Clauses deleted for lack of memory   : 0
% 0.20/0.46  # Backward-subsumed                    : 15
% 0.20/0.46  # Backward-rewritten                   : 40
% 0.20/0.46  # Generated clauses                    : 852
% 0.20/0.46  # ...of the previous two non-trivial   : 798
% 0.20/0.46  # Contextual simplify-reflections      : 17
% 0.20/0.46  # Paramodulations                      : 844
% 0.20/0.46  # Factorizations                       : 4
% 0.20/0.46  # Equation resolutions                 : 6
% 0.20/0.46  # Propositional unsat checks           : 0
% 0.20/0.46  #    Propositional check models        : 0
% 0.20/0.46  #    Propositional check unsatisfiable : 0
% 0.20/0.46  #    Propositional clauses             : 0
% 0.20/0.46  #    Propositional clauses after purity: 0
% 0.20/0.46  #    Propositional unsat core size     : 0
% 0.20/0.46  #    Propositional preprocessing time  : 0.000
% 0.20/0.46  #    Propositional encoding time       : 0.000
% 0.20/0.46  #    Propositional solver time         : 0.000
% 0.20/0.46  #    Success case prop preproc time    : 0.000
% 0.20/0.46  #    Success case prop encoding time   : 0.000
% 0.20/0.46  #    Success case prop solver time     : 0.000
% 0.20/0.46  # Current number of processed clauses  : 332
% 0.20/0.46  #    Positive orientable unit clauses  : 23
% 0.20/0.46  #    Positive unorientable unit clauses: 0
% 0.20/0.46  #    Negative unit clauses             : 5
% 0.20/0.46  #    Non-unit-clauses                  : 304
% 0.20/0.46  # Current number of unprocessed clauses: 233
% 0.20/0.46  # ...number of literals in the above   : 1489
% 0.20/0.46  # Current number of archived formulas  : 0
% 0.20/0.46  # Current number of archived clauses   : 96
% 0.20/0.46  # Clause-clause subsumption calls (NU) : 33085
% 0.20/0.46  # Rec. Clause-clause subsumption calls : 6969
% 0.20/0.46  # Non-unit clause-clause subsumptions  : 219
% 0.20/0.46  # Unit Clause-clause subsumption calls : 816
% 0.20/0.46  # Rewrite failures with RHS unbound    : 0
% 0.20/0.46  # BW rewrite match attempts            : 4
% 0.20/0.46  # BW rewrite match successes           : 4
% 0.20/0.46  # Condensation attempts                : 0
% 0.20/0.46  # Condensation successes               : 0
% 0.20/0.46  # Termbank termtop insertions          : 41725
% 0.20/0.46  
% 0.20/0.46  # -------------------------------------------------
% 0.20/0.46  # User time                : 0.107 s
% 0.20/0.46  # System time              : 0.008 s
% 0.20/0.46  # Total time               : 0.115 s
% 0.20/0.46  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
