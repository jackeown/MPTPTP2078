%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1802+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:47 EST 2020

% Result     : Theorem 0.55s
% Output     : CNFRefutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 852 expanded)
%              Number of clauses        :   70 ( 290 expanded)
%              Number of leaves         :   15 ( 214 expanded)
%              Depth                    :   18
%              Number of atoms          :  574 (6437 expanded)
%              Number of equality atoms :   51 ( 193 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    6 (   2 average)

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

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

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

fof(t118_tmap_1,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_tmap_1)).

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

fof(dt_k9_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_funct_1(k9_tmap_1(X1,X2))
        & v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
        & m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).

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

fof(fc4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_struct_0(k6_tmap_1(X1,X2))
        & v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(t109_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r1_xboole_0(u1_struct_0(X3),X2)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X3))
                   => r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tmap_1)).

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

fof(d3_tsep_1,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ( r1_tsep_1(X1,X2)
          <=> r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(c_0_15,plain,(
    ! [X7,X8,X9,X10] :
      ( ( X9 != k8_tmap_1(X7,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X7)))
        | X10 != u1_struct_0(X8)
        | X9 = k6_tmap_1(X7,X10)
        | ~ v1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9)
        | ~ m1_pre_topc(X8,X7)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk1_3(X7,X8,X9),k1_zfmisc_1(u1_struct_0(X7)))
        | X9 = k8_tmap_1(X7,X8)
        | ~ v1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9)
        | ~ m1_pre_topc(X8,X7)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( esk1_3(X7,X8,X9) = u1_struct_0(X8)
        | X9 = k8_tmap_1(X7,X8)
        | ~ v1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9)
        | ~ m1_pre_topc(X8,X7)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( X9 != k6_tmap_1(X7,esk1_3(X7,X8,X9))
        | X9 = k8_tmap_1(X7,X8)
        | ~ v1_pre_topc(X9)
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9)
        | ~ m1_pre_topc(X8,X7)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_16,plain,(
    ! [X45,X46] :
      ( ~ l1_pre_topc(X45)
      | ~ m1_pre_topc(X46,X45)
      | m1_subset_1(u1_struct_0(X46),k1_zfmisc_1(u1_struct_0(X45))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_17,plain,(
    ! [X19,X20] :
      ( ( v1_funct_1(k7_tmap_1(X19,X20))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19))) )
      & ( v1_funct_2(k7_tmap_1(X19,X20),u1_struct_0(X19),u1_struct_0(k6_tmap_1(X19,X20)))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19))) )
      & ( m1_subset_1(k7_tmap_1(X19,X20),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(k6_tmap_1(X19,X20)))))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t118_tmap_1])).

cnf(c_0_19,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X21,X22] :
      ( ( v1_pre_topc(k8_tmap_1(X21,X22))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_pre_topc(X22,X21) )
      & ( v2_pre_topc(k8_tmap_1(X21,X22))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_pre_topc(X22,X21) )
      & ( l1_pre_topc(k8_tmap_1(X21,X22))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_pre_topc(X22,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

cnf(c_0_22,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk3_0)
    & r1_tsep_1(esk4_0,esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & ~ r1_tmap_1(esk5_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk5_0),esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

cnf(c_0_24,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_26,plain,(
    ! [X23,X24] :
      ( ( v1_funct_1(k9_tmap_1(X23,X24))
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | ~ m1_pre_topc(X24,X23) )
      & ( v1_funct_2(k9_tmap_1(X23,X24),u1_struct_0(X23),u1_struct_0(k8_tmap_1(X23,X24)))
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | ~ m1_pre_topc(X24,X23) )
      & ( m1_subset_1(k9_tmap_1(X23,X24),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(k8_tmap_1(X23,X24)))))
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | ~ m1_pre_topc(X24,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

cnf(c_0_27,plain,
    ( X1 = k6_tmap_1(X2,u1_struct_0(X3))
    | v2_struct_0(X2)
    | u1_struct_0(X3) != u1_struct_0(X4)
    | X1 != k8_tmap_1(X2,X4)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_31,plain,(
    ! [X33,X34,X35,X36,X37,X38] :
      ( ( ~ r1_funct_2(X33,X34,X35,X36,X37,X38)
        | X37 = X38
        | v1_xboole_0(X34)
        | v1_xboole_0(X36)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X33,X34)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,X35,X36)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( X37 != X38
        | r1_funct_2(X33,X34,X35,X36,X37,X38)
        | v1_xboole_0(X34)
        | v1_xboole_0(X36)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X33,X34)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,X35,X36)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_32,plain,
    ( m1_subset_1(k7_tmap_1(X1,u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( v1_funct_2(k7_tmap_1(X1,u1_struct_0(X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_20])).

cnf(c_0_38,plain,
    ( v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_20])).

fof(c_0_39,plain,(
    ! [X12,X13,X14,X15] :
      ( ( X14 != k9_tmap_1(X12,X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X12)))
        | X15 != u1_struct_0(X13)
        | r1_funct_2(u1_struct_0(X12),u1_struct_0(k8_tmap_1(X12,X13)),u1_struct_0(X12),u1_struct_0(k6_tmap_1(X12,X15)),X14,k7_tmap_1(X12,X15))
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(k8_tmap_1(X12,X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(k8_tmap_1(X12,X13)))))
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk2_3(X12,X13,X14),k1_zfmisc_1(u1_struct_0(X12)))
        | X14 = k9_tmap_1(X12,X13)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(k8_tmap_1(X12,X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(k8_tmap_1(X12,X13)))))
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( esk2_3(X12,X13,X14) = u1_struct_0(X13)
        | X14 = k9_tmap_1(X12,X13)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(k8_tmap_1(X12,X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(k8_tmap_1(X12,X13)))))
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r1_funct_2(u1_struct_0(X12),u1_struct_0(k8_tmap_1(X12,X13)),u1_struct_0(X12),u1_struct_0(k6_tmap_1(X12,esk2_3(X12,X13,X14))),X14,k7_tmap_1(X12,esk2_3(X12,X13,X14)))
        | X14 = k9_tmap_1(X12,X13)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(k8_tmap_1(X12,X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(k8_tmap_1(X12,X13)))))
        | ~ m1_pre_topc(X13,X12)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_tmap_1])])])])])])).

cnf(c_0_40,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_43,plain,
    ( k8_tmap_1(X1,X2) = k6_tmap_1(X1,u1_struct_0(X3))
    | v2_struct_0(X1)
    | u1_struct_0(X3) != u1_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_44,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,u1_struct_0(esk4_0)))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,u1_struct_0(esk4_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_48,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_52,negated_conjecture,
    ( k6_tmap_1(esk3_0,u1_struct_0(X1)) = k8_tmap_1(esk3_0,esk4_0)
    | u1_struct_0(X1) != u1_struct_0(esk4_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_53,negated_conjecture,
    ( X1 = k7_tmap_1(esk3_0,u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(k6_tmap_1(esk3_0,u1_struct_0(esk4_0))))
    | v1_xboole_0(X2)
    | ~ r1_funct_2(X3,X2,u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,u1_struct_0(esk4_0))),X1,k7_tmap_1(esk3_0,u1_struct_0(esk4_0)))
    | ~ v1_funct_2(X1,X3,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_54,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk3_0),u1_struct_0(k6_tmap_1(esk3_0,X1)),k9_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,X1))
    | X1 != u1_struct_0(esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

fof(c_0_55,plain,(
    ! [X29,X30] :
      ( ( ~ v2_struct_0(k6_tmap_1(X29,X30))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( v1_pre_topc(k6_tmap_1(X29,X30))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( v2_pre_topc(k6_tmap_1(X29,X30))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_tmap_1])])])])).

cnf(c_0_56,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_52]),c_0_33])])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_52]),c_0_33])])).

cnf(c_0_59,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(esk3_0,u1_struct_0(esk4_0))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_50]),c_0_51]),c_0_49])])).

fof(c_0_60,plain,(
    ! [X41,X42,X43,X44] :
      ( v2_struct_0(X41)
      | ~ v2_pre_topc(X41)
      | ~ l1_pre_topc(X41)
      | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
      | v2_struct_0(X43)
      | ~ m1_pre_topc(X43,X41)
      | ~ r1_xboole_0(u1_struct_0(X43),X42)
      | ~ m1_subset_1(X44,u1_struct_0(X43))
      | r1_tmap_1(X43,k6_tmap_1(X41,X42),k2_tmap_1(X41,k6_tmap_1(X41,X42),k7_tmap_1(X41,X42),X43),X44) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t109_tmap_1])])])])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | m1_subset_1(esk2_3(esk3_0,esk4_0,k7_tmap_1(esk3_0,u1_struct_0(esk4_0))),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_47]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_63,plain,
    ( esk2_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_64,plain,(
    ! [X28] :
      ( v2_struct_0(X28)
      | ~ l1_struct_0(X28)
      | ~ v1_xboole_0(u1_struct_0(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_65,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | v1_xboole_0(u1_struct_0(k6_tmap_1(esk3_0,u1_struct_0(esk4_0))))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_20]),c_0_33]),c_0_34])])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X3)
    | r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | ~ r1_xboole_0(u1_struct_0(X3),X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | ~ v2_struct_0(k6_tmap_1(esk3_0,esk2_3(esk3_0,esk4_0,k7_tmap_1(esk3_0,u1_struct_0(esk4_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_68,negated_conjecture,
    ( esk2_3(esk3_0,esk4_0,k7_tmap_1(esk3_0,u1_struct_0(esk4_0))) = u1_struct_0(esk4_0)
    | k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_57]),c_0_58]),c_0_47]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_69,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_52]),c_0_33])])).

fof(c_0_71,plain,(
    ! [X25] :
      ( ~ l1_pre_topc(X25)
      | l1_struct_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_72,plain,
    ( r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(X3)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(X3)),k7_tmap_1(X2,u1_struct_0(X3)),X1),X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_20])).

cnf(c_0_73,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | ~ v2_struct_0(k6_tmap_1(esk3_0,u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | v2_struct_0(k8_tmap_1(esk3_0,esk4_0))
    | ~ l1_struct_0(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_77,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(esk3_0,u1_struct_0(esk4_0)),k2_tmap_1(esk3_0,k6_tmap_1(esk3_0,u1_struct_0(esk4_0)),k9_tmap_1(esk3_0,esk4_0),X1),X2)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ v2_struct_0(k6_tmap_1(esk3_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_78,negated_conjecture,
    ( r1_tmap_1(X1,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(X2)),X1),X3)
    | v2_struct_0(X1)
    | u1_struct_0(X2) != u1_struct_0(esk4_0)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X2,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_52]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_79,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | v2_struct_0(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])])).

cnf(c_0_80,negated_conjecture,
    ( r1_tmap_1(X1,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1),X2)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ v2_struct_0(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_52]),c_0_33])])).

fof(c_0_81,plain,(
    ! [X17,X18] :
      ( ( ~ r1_tsep_1(X17,X18)
        | r1_xboole_0(u1_struct_0(X17),u1_struct_0(X18))
        | ~ l1_struct_0(X18)
        | ~ l1_struct_0(X17) )
      & ( ~ r1_xboole_0(u1_struct_0(X17),u1_struct_0(X18))
        | r1_tsep_1(X17,X18)
        | ~ l1_struct_0(X18)
        | ~ l1_struct_0(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).

fof(c_0_82,plain,(
    ! [X26,X27] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_pre_topc(X27,X26)
      | l1_pre_topc(X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_83,negated_conjecture,
    ( r1_tmap_1(X1,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1),X2)
    | v2_struct_0(X1)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_33])]),c_0_80])).

cnf(c_0_84,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_85,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( r1_tmap_1(X1,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1),X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk4_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_33]),c_0_34])])).

cnf(c_0_88,negated_conjecture,
    ( r1_tmap_1(X1,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1),X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X1,esk4_0)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_75]),c_0_87])])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_90,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_91,negated_conjecture,
    ( ~ r1_tmap_1(esk5_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk5_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_92,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_93,plain,(
    ! [X39,X40] :
      ( ~ l1_struct_0(X39)
      | ~ l1_struct_0(X40)
      | ~ r1_tsep_1(X39,X40)
      | r1_tsep_1(X40,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

cnf(c_0_94,negated_conjecture,
    ( ~ r1_tsep_1(esk5_0,esk4_0)
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])]),c_0_91]),c_0_92])).

cnf(c_0_95,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_96,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_97,negated_conjecture,
    ( ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96])])).

cnf(c_0_98,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_90]),c_0_34])])).

cnf(c_0_99,negated_conjecture,
    ( ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_75]),c_0_98])])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_75]),c_0_87])]),
    [proof]).

%------------------------------------------------------------------------------
