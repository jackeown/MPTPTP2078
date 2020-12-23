%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:19 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 491 expanded)
%              Number of clauses        :   61 ( 187 expanded)
%              Number of leaves         :   18 ( 120 expanded)
%              Depth                    :   13
%              Number of atoms          :  375 (3381 expanded)
%              Number of equality atoms :   36 ( 249 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t60_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X2) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
                 => ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                   => r1_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,k2_tmap_1(X2,X1,X4,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_tmap_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(t11_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(d4_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(fc6_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

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

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X2) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
                   => ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                     => r1_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,k2_tmap_1(X2,X1,X4,X3)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t60_tmap_1])).

fof(c_0_19,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_20,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_21,plain,(
    ! [X30,X31] :
      ( ( ~ m1_pre_topc(X30,X31)
        | m1_pre_topc(X30,g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))
        | ~ l1_pre_topc(X31)
        | ~ l1_pre_topc(X30) )
      & ( ~ m1_pre_topc(X30,g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))
        | m1_pre_topc(X30,X31)
        | ~ l1_pre_topc(X31)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

fof(c_0_22,plain,(
    ! [X24,X25] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_pre_topc(X25,X24)
      | l1_pre_topc(X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    & g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    & ~ r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0),u1_struct_0(esk1_0),esk4_0,k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( X1 = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_31,plain,(
    ! [X47,X48] :
      ( ~ l1_pre_topc(X47)
      | ~ m1_pre_topc(X48,X47)
      | m1_subset_1(u1_struct_0(X48),k1_zfmisc_1(u1_struct_0(X47))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_32,plain,(
    ! [X44,X45,X46] :
      ( ( ~ m1_pre_topc(X45,X44)
        | m1_pre_topc(X46,X44)
        | X45 != g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45)
        | ~ l1_pre_topc(X44) )
      & ( ~ m1_pre_topc(X46,X44)
        | m1_pre_topc(X45,X44)
        | X45 != g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45)
        | ~ l1_pre_topc(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_tmap_1])])])])).

fof(c_0_33,plain,(
    ! [X28,X29] :
      ( ~ l1_pre_topc(X28)
      | ~ m1_pre_topc(X29,g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28)))
      | m1_pre_topc(X29,X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

cnf(c_0_34,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

fof(c_0_37,plain,(
    ! [X42,X43] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X43),u1_pre_topc(X43)))
        | ~ m1_pre_topc(X43,X42)
        | ~ l1_pre_topc(X42) )
      & ( m1_pre_topc(g1_pre_topc(u1_struct_0(X43),u1_pre_topc(X43)),X42)
        | ~ m1_pre_topc(X43,X42)
        | ~ l1_pre_topc(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).

fof(c_0_38,plain,(
    ! [X38,X39,X40,X41] :
      ( v2_struct_0(X38)
      | ~ v2_pre_topc(X38)
      | ~ l1_pre_topc(X38)
      | v2_struct_0(X39)
      | ~ v2_pre_topc(X39)
      | ~ l1_pre_topc(X39)
      | ~ v1_funct_1(X40)
      | ~ v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X39))
      | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X39))))
      | ~ m1_pre_topc(X41,X38)
      | k2_tmap_1(X38,X39,X40,X41) = k2_partfun1(u1_struct_0(X38),u1_struct_0(X39),X40,u1_struct_0(X41)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_39,plain,
    ( X1 = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_25])).

cnf(c_0_40,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | X1 != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_42,plain,(
    ! [X27] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)))
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( v2_pre_topc(g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)))
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).

cnf(c_0_43,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_45,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_46,plain,(
    ! [X19,X20,X21,X22] :
      ( ~ v1_funct_1(X21)
      | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k2_partfun1(X19,X20,X21,X22) = k7_relat_1(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_50,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_51,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_52,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_54,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_55,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_56,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_57,plain,
    ( m1_pre_topc(X1,X2)
    | X3 != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_41,c_0_27])).

cnf(c_0_58,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_59,negated_conjecture,
    ( m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_29])])).

cnf(c_0_60,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_35])).

fof(c_0_61,plain,(
    ! [X32,X33,X34,X35,X36,X37] :
      ( ( ~ r1_funct_2(X32,X33,X34,X35,X36,X37)
        | X36 = X37
        | v1_xboole_0(X33)
        | v1_xboole_0(X35)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,X32,X33)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X34,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X36 != X37
        | r1_funct_2(X32,X33,X34,X35,X36,X37)
        | v1_xboole_0(X33)
        | v1_xboole_0(X35)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,X32,X33)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X34,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_62,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_63,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,u1_struct_0(X1)) = k2_tmap_1(esk2_0,esk1_0,esk4_0,X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_29]),c_0_53])]),c_0_54]),c_0_55])).

fof(c_0_64,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | v1_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_65,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_40]),c_0_27])).

cnf(c_0_66,negated_conjecture,
    ( m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_35]),c_0_36])])).

cnf(c_0_67,plain,
    ( m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_57]),c_0_58])).

cnf(c_0_68,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk2_0)
    | ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_36])])).

cnf(c_0_69,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0),u1_struct_0(esk1_0),esk4_0,k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_71,negated_conjecture,
    ( k2_tmap_1(esk2_0,esk1_0,esk4_0,X1) = k7_relat_1(esk4_0,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_53]),c_0_48])])).

fof(c_0_72,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X12)
      | ~ v4_relat_1(X12,X11)
      | X12 = k7_relat_1(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_73,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk2_0)
    | ~ m1_pre_topc(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_28]),c_0_36])])).

cnf(c_0_75,negated_conjecture,
    ( m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_34]),c_0_29])])).

cnf(c_0_76,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk2_0)
    | ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_51]),c_0_29])])).

fof(c_0_77,plain,(
    ! [X16,X17,X18] :
      ( ( v4_relat_1(X18,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( v5_relat_1(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_78,plain,
    ( r1_funct_2(X1,X2,X3,X4,X5,X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | ~ v1_funct_2(X5,X3,X4)
    | ~ v1_funct_2(X5,X1,X2)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0),u1_struct_0(esk1_0),esk4_0,k7_relat_1(esk4_0,u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_28])])).

cnf(c_0_80,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_48])).

cnf(c_0_82,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk2_0)
    | ~ m1_pre_topc(esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_83,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_75]),c_0_28])])).

cnf(c_0_84,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

fof(c_0_85,plain,(
    ! [X26] :
      ( v2_struct_0(X26)
      | ~ l1_struct_0(X26)
      | ~ v1_xboole_0(u1_struct_0(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_86,plain,(
    ! [X23] :
      ( ~ l1_pre_topc(X23)
      | l1_struct_0(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_87,negated_conjecture,
    ( r1_funct_2(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk4_0)
    | v1_xboole_0(u1_struct_0(esk1_0))
    | v1_xboole_0(X2)
    | ~ v1_funct_2(esk4_0,X1,X2)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_48]),c_0_49]),c_0_53])])).

cnf(c_0_88,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0),u1_struct_0(esk1_0),esk4_0,esk4_0)
    | ~ v4_relat_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])])).

cnf(c_0_89,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83])])).

cnf(c_0_90,negated_conjecture,
    ( v4_relat_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_48])).

cnf(c_0_91,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_92,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk4_0)
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_48]),c_0_49])])).

cnf(c_0_94,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89]),c_0_89]),c_0_90])])).

cnf(c_0_95,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_96,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_52])]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.13/0.40  # and selection function PSelectComplexExceptRRHorn.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.031 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t60_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=>r1_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,k2_tmap_1(X2,X1,X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 0.13/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.40  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.13/0.40  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.40  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.13/0.40  fof(t12_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:((v2_pre_topc(X3)&l1_pre_topc(X3))=>(X2=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=>(m1_pre_topc(X2,X1)<=>m1_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tmap_1)).
% 0.13/0.40  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.13/0.40  fof(t11_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))&m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 0.13/0.40  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.13/0.40  fof(fc6_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 0.13/0.40  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.13/0.40  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 0.13/0.40  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.40  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.13/0.40  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.13/0.40  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.13/0.40  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.40  fof(c_0_18, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=>r1_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,k2_tmap_1(X2,X1,X4,X3)))))))), inference(assume_negation,[status(cth)],[t60_tmap_1])).
% 0.13/0.40  fof(c_0_19, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.40  fof(c_0_20, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.40  fof(c_0_21, plain, ![X30, X31]:((~m1_pre_topc(X30,X31)|m1_pre_topc(X30,g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))|~l1_pre_topc(X31)|~l1_pre_topc(X30))&(~m1_pre_topc(X30,g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))|m1_pre_topc(X30,X31)|~l1_pre_topc(X31)|~l1_pre_topc(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.13/0.40  fof(c_0_22, plain, ![X24, X25]:(~l1_pre_topc(X24)|(~m1_pre_topc(X25,X24)|l1_pre_topc(X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.40  fof(c_0_23, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))))&(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))&~r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0),u1_struct_0(esk1_0),esk4_0,k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 0.13/0.40  cnf(c_0_24, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.40  cnf(c_0_26, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.40  cnf(c_0_27, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_28, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_30, plain, (X1=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.40  fof(c_0_31, plain, ![X47, X48]:(~l1_pre_topc(X47)|(~m1_pre_topc(X48,X47)|m1_subset_1(u1_struct_0(X48),k1_zfmisc_1(u1_struct_0(X47))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.13/0.40  fof(c_0_32, plain, ![X44, X45, X46]:((~m1_pre_topc(X45,X44)|m1_pre_topc(X46,X44)|X45!=g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))|(~v2_pre_topc(X46)|~l1_pre_topc(X46))|(~v2_pre_topc(X45)|~l1_pre_topc(X45))|~l1_pre_topc(X44))&(~m1_pre_topc(X46,X44)|m1_pre_topc(X45,X44)|X45!=g1_pre_topc(u1_struct_0(X46),u1_pre_topc(X46))|(~v2_pre_topc(X46)|~l1_pre_topc(X46))|(~v2_pre_topc(X45)|~l1_pre_topc(X45))|~l1_pre_topc(X44))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_tmap_1])])])])).
% 0.13/0.40  fof(c_0_33, plain, ![X28, X29]:(~l1_pre_topc(X28)|(~m1_pre_topc(X29,g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28)))|m1_pre_topc(X29,X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.13/0.40  cnf(c_0_34, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.40  cnf(c_0_35, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_36, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.13/0.40  fof(c_0_37, plain, ![X42, X43]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X43),u1_pre_topc(X43)))|~m1_pre_topc(X43,X42)|~l1_pre_topc(X42))&(m1_pre_topc(g1_pre_topc(u1_struct_0(X43),u1_pre_topc(X43)),X42)|~m1_pre_topc(X43,X42)|~l1_pre_topc(X42))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).
% 0.13/0.40  fof(c_0_38, plain, ![X38, X39, X40, X41]:(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|(~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X39))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X39))))|(~m1_pre_topc(X41,X38)|k2_tmap_1(X38,X39,X40,X41)=k2_partfun1(u1_struct_0(X38),u1_struct_0(X39),X40,u1_struct_0(X41)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.13/0.40  cnf(c_0_39, plain, (X1=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_25])).
% 0.13/0.40  cnf(c_0_40, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.40  cnf(c_0_41, plain, (m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)|X1!=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.40  fof(c_0_42, plain, ![X27]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)))|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))&(v2_pre_topc(g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)))|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).
% 0.13/0.40  cnf(c_0_43, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.40  cnf(c_0_44, negated_conjecture, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.13/0.40  cnf(c_0_45, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.40  fof(c_0_46, plain, ![X19, X20, X21, X22]:(~v1_funct_1(X21)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|k2_partfun1(X19,X20,X21,X22)=k7_relat_1(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.13/0.40  cnf(c_0_47, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.40  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_49, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_50, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_51, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_52, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_53, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_54, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_55, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_56, plain, (u1_struct_0(X1)=u1_struct_0(X2)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.40  cnf(c_0_57, plain, (m1_pre_topc(X1,X2)|X3!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~v2_pre_topc(X3)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_41, c_0_27])).
% 0.13/0.40  cnf(c_0_58, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.40  cnf(c_0_59, negated_conjecture, (m1_pre_topc(X1,esk2_0)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_29])])).
% 0.13/0.40  cnf(c_0_60, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_45, c_0_35])).
% 0.13/0.40  fof(c_0_61, plain, ![X32, X33, X34, X35, X36, X37]:((~r1_funct_2(X32,X33,X34,X35,X36,X37)|X36=X37|(v1_xboole_0(X33)|v1_xboole_0(X35)|~v1_funct_1(X36)|~v1_funct_2(X36,X32,X33)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|~v1_funct_1(X37)|~v1_funct_2(X37,X34,X35)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))&(X36!=X37|r1_funct_2(X32,X33,X34,X35,X36,X37)|(v1_xboole_0(X33)|v1_xboole_0(X35)|~v1_funct_1(X36)|~v1_funct_2(X36,X32,X33)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|~v1_funct_1(X37)|~v1_funct_2(X37,X34,X35)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 0.13/0.40  cnf(c_0_62, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.40  cnf(c_0_63, negated_conjecture, (k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,u1_struct_0(X1))=k2_tmap_1(esk2_0,esk1_0,esk4_0,X1)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_29]), c_0_53])]), c_0_54]), c_0_55])).
% 0.13/0.40  fof(c_0_64, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|v1_relat_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.40  cnf(c_0_65, plain, (u1_struct_0(X1)=u1_struct_0(X2)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_40]), c_0_27])).
% 0.13/0.40  cnf(c_0_66, negated_conjecture, (m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_35]), c_0_36])])).
% 0.13/0.40  cnf(c_0_67, plain, (m1_pre_topc(X1,X2)|~v2_pre_topc(X1)|~m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_57]), c_0_58])).
% 0.13/0.40  cnf(c_0_68, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)),esk2_0)|~m1_pre_topc(esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_36])])).
% 0.13/0.40  cnf(c_0_69, plain, (r1_funct_2(X3,X4,X5,X6,X1,X2)|v1_xboole_0(X4)|v1_xboole_0(X6)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X5,X6)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.13/0.40  cnf(c_0_70, negated_conjecture, (~r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0),u1_struct_0(esk1_0),esk4_0,k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_71, negated_conjecture, (k2_tmap_1(esk2_0,esk1_0,esk4_0,X1)=k7_relat_1(esk4_0,u1_struct_0(X1))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_53]), c_0_48])])).
% 0.13/0.40  fof(c_0_72, plain, ![X11, X12]:(~v1_relat_1(X12)|~v4_relat_1(X12,X11)|X12=k7_relat_1(X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.13/0.40  cnf(c_0_73, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.13/0.40  cnf(c_0_74, negated_conjecture, (u1_struct_0(esk3_0)=u1_struct_0(esk2_0)|~m1_pre_topc(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_28]), c_0_36])])).
% 0.13/0.40  cnf(c_0_75, negated_conjecture, (m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_34]), c_0_29])])).
% 0.13/0.40  cnf(c_0_76, negated_conjecture, (m1_pre_topc(esk2_0,esk2_0)|~m1_pre_topc(esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_51]), c_0_29])])).
% 0.13/0.40  fof(c_0_77, plain, ![X16, X17, X18]:((v4_relat_1(X18,X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))&(v5_relat_1(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.13/0.40  cnf(c_0_78, plain, (r1_funct_2(X1,X2,X3,X4,X5,X5)|v1_xboole_0(X4)|v1_xboole_0(X2)|~v1_funct_2(X5,X3,X4)|~v1_funct_2(X5,X1,X2)|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_69])).
% 0.13/0.40  cnf(c_0_79, negated_conjecture, (~r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0),u1_struct_0(esk1_0),esk4_0,k7_relat_1(esk4_0,u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_28])])).
% 0.13/0.40  cnf(c_0_80, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.13/0.40  cnf(c_0_81, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_73, c_0_48])).
% 0.13/0.40  cnf(c_0_82, negated_conjecture, (u1_struct_0(esk3_0)=u1_struct_0(esk2_0)|~m1_pre_topc(esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.13/0.40  cnf(c_0_83, negated_conjecture, (m1_pre_topc(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_75]), c_0_28])])).
% 0.13/0.40  cnf(c_0_84, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.13/0.40  fof(c_0_85, plain, ![X26]:(v2_struct_0(X26)|~l1_struct_0(X26)|~v1_xboole_0(u1_struct_0(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.13/0.40  fof(c_0_86, plain, ![X23]:(~l1_pre_topc(X23)|l1_struct_0(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.40  cnf(c_0_87, negated_conjecture, (r1_funct_2(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk4_0)|v1_xboole_0(u1_struct_0(esk1_0))|v1_xboole_0(X2)|~v1_funct_2(esk4_0,X1,X2)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_48]), c_0_49]), c_0_53])])).
% 0.13/0.40  cnf(c_0_88, negated_conjecture, (~r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0),u1_struct_0(esk1_0),esk4_0,esk4_0)|~v4_relat_1(esk4_0,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])])).
% 0.13/0.40  cnf(c_0_89, negated_conjecture, (u1_struct_0(esk3_0)=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83])])).
% 0.13/0.40  cnf(c_0_90, negated_conjecture, (v4_relat_1(esk4_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_84, c_0_48])).
% 0.13/0.40  cnf(c_0_91, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.13/0.40  cnf(c_0_92, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.13/0.40  cnf(c_0_93, negated_conjecture, (r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk4_0)|v1_xboole_0(u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_48]), c_0_49])])).
% 0.13/0.40  cnf(c_0_94, negated_conjecture, (~r1_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_89]), c_0_89]), c_0_90])])).
% 0.13/0.40  cnf(c_0_95, plain, (v2_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.13/0.40  cnf(c_0_96, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))), inference(sr,[status(thm)],[c_0_93, c_0_94])).
% 0.13/0.40  cnf(c_0_97, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_52])]), c_0_54]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 98
% 0.13/0.40  # Proof object clause steps            : 61
% 0.13/0.40  # Proof object formula steps           : 37
% 0.13/0.40  # Proof object conjectures             : 38
% 0.13/0.40  # Proof object clause conjectures      : 35
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 29
% 0.13/0.40  # Proof object initial formulas used   : 18
% 0.13/0.40  # Proof object generating inferences   : 26
% 0.13/0.40  # Proof object simplifying inferences  : 55
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 18
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 39
% 0.13/0.40  # Removed in clause preprocessing      : 0
% 0.13/0.40  # Initial clauses in saturation        : 39
% 0.13/0.40  # Processed clauses                    : 317
% 0.13/0.40  # ...of these trivial                  : 7
% 0.13/0.40  # ...subsumed                          : 99
% 0.13/0.40  # ...remaining for further processing  : 211
% 0.13/0.40  # Other redundant clauses eliminated   : 3
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 10
% 0.13/0.40  # Backward-rewritten                   : 67
% 0.13/0.40  # Generated clauses                    : 508
% 0.13/0.40  # ...of the previous two non-trivial   : 497
% 0.13/0.40  # Contextual simplify-reflections      : 6
% 0.13/0.40  # Paramodulations                      : 496
% 0.13/0.40  # Factorizations                       : 6
% 0.13/0.40  # Equation resolutions                 : 5
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 93
% 0.13/0.40  #    Positive orientable unit clauses  : 27
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 5
% 0.13/0.40  #    Non-unit-clauses                  : 61
% 0.13/0.40  # Current number of unprocessed clauses: 246
% 0.13/0.40  # ...number of literals in the above   : 958
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 115
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 4428
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 3269
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 107
% 0.13/0.40  # Unit Clause-clause subsumption calls : 103
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 28
% 0.13/0.40  # BW rewrite match successes           : 12
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 15337
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.054 s
% 0.13/0.40  # System time              : 0.005 s
% 0.13/0.40  # Total time               : 0.059 s
% 0.13/0.40  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
