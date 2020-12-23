%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1803+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:48 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  110 (6196 expanded)
%              Number of clauses        :   79 (1999 expanded)
%              Number of leaves         :   15 (1578 expanded)
%              Depth                    :   19
%              Number of atoms          :  589 (39081 expanded)
%              Number of equality atoms :   74 (1841 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t114_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
            & ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => u1_pre_topc(k8_tmap_1(X1,X2)) = k5_tmap_1(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_tmap_1)).

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

fof(fc4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_struct_0(k6_tmap_1(X1,X2))
        & v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

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

fof(c_0_17,plain,(
    ! [X25,X26] :
      ( ( v1_pre_topc(k8_tmap_1(X25,X26))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_pre_topc(X26,X25) )
      & ( v2_pre_topc(k8_tmap_1(X25,X26))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_pre_topc(X26,X25) )
      & ( l1_pre_topc(k8_tmap_1(X25,X26))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_pre_topc(X26,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

fof(c_0_18,plain,(
    ! [X52,X53] :
      ( ~ l1_pre_topc(X52)
      | ~ m1_pre_topc(X53,X52)
      | m1_subset_1(u1_struct_0(X53),k1_zfmisc_1(u1_struct_0(X52))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_19,plain,(
    ! [X49,X50,X51] :
      ( ( u1_struct_0(k8_tmap_1(X49,X50)) = u1_struct_0(X49)
        | v2_struct_0(X50)
        | ~ m1_pre_topc(X50,X49)
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49) )
      & ( ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))
        | X51 != u1_struct_0(X50)
        | u1_pre_topc(k8_tmap_1(X49,X50)) = k5_tmap_1(X49,X51)
        | v2_struct_0(X50)
        | ~ m1_pre_topc(X50,X49)
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t114_tmap_1])])])])])).

fof(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & ~ r1_tmap_1(esk4_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),esk5_0) ),
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
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
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

cnf(c_0_27,plain,
    ( u1_struct_0(k8_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_33,plain,(
    ! [X23,X24] :
      ( ( v1_funct_1(k7_tmap_1(X23,X24))
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23))) )
      & ( v1_funct_2(k7_tmap_1(X23,X24),u1_struct_0(X23),u1_struct_0(k6_tmap_1(X23,X24)))
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23))) )
      & ( m1_subset_1(k7_tmap_1(X23,X24),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(k6_tmap_1(X23,X24)))))
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

cnf(c_0_34,plain,
    ( k6_tmap_1(X1,u1_struct_0(X2)) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_21])]),c_0_22]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( u1_struct_0(k8_tmap_1(esk3_0,esk4_0)) = u1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])]),c_0_31]),c_0_32])).

cnf(c_0_37,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k6_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k8_tmap_1(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_28]),c_0_29]),c_0_30])]),c_0_32])).

cnf(c_0_39,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( esk2_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k9_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( X1 = k9_tmap_1(esk3_0,esk4_0)
    | m1_subset_1(esk2_3(esk3_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_28]),c_0_29]),c_0_30])]),c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_36]),c_0_29]),c_0_30])]),c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),u1_struct_0(esk3_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_38]),c_0_36]),c_0_29]),c_0_30])]),c_0_32])).

cnf(c_0_45,plain,
    ( v1_funct_1(k7_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_25])).

cnf(c_0_46,negated_conjecture,
    ( esk2_3(esk3_0,esk4_0,X1) = u1_struct_0(esk4_0)
    | X1 = k9_tmap_1(esk3_0,esk4_0)
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_36]),c_0_28]),c_0_29]),c_0_30])]),c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | m1_subset_1(esk2_3(esk3_0,esk4_0,k7_tmap_1(esk3_0,u1_struct_0(esk4_0))),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v1_funct_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_28]),c_0_29]),c_0_30])]),c_0_32])).

cnf(c_0_49,negated_conjecture,
    ( esk2_3(esk3_0,esk4_0,k7_tmap_1(esk3_0,u1_struct_0(esk4_0))) = u1_struct_0(esk4_0)
    | k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | ~ v1_funct_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_43]),c_0_44])).

fof(c_0_50,plain,(
    ! [X45,X46,X47,X48] :
      ( v2_struct_0(X45)
      | ~ v2_pre_topc(X45)
      | ~ l1_pre_topc(X45)
      | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
      | v2_struct_0(X47)
      | ~ m1_pre_topc(X47,X45)
      | u1_struct_0(X47) != X46
      | ~ m1_subset_1(X48,u1_struct_0(X47))
      | r1_tmap_1(X47,k6_tmap_1(X45,X46),k2_tmap_1(X45,k6_tmap_1(X45,X46),k7_tmap_1(X45,X46),X47),X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t110_tmap_1])])])])).

cnf(c_0_51,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | m1_subset_1(esk2_3(esk3_0,esk4_0,k7_tmap_1(esk3_0,u1_struct_0(esk4_0))),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])])).

cnf(c_0_52,negated_conjecture,
    ( esk2_3(esk3_0,esk4_0,k7_tmap_1(esk3_0,u1_struct_0(esk4_0))) = u1_struct_0(esk4_0)
    | k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_48])])).

fof(c_0_53,plain,(
    ! [X33,X34] :
      ( ( ~ v2_struct_0(k6_tmap_1(X33,X34))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))) )
      & ( v1_pre_topc(k6_tmap_1(X33,X34))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))) )
      & ( v2_pre_topc(k6_tmap_1(X33,X34))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_tmap_1])])])])).

cnf(c_0_54,plain,
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

cnf(c_0_55,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | m1_subset_1(esk2_3(esk3_0,esk4_0,k7_tmap_1(esk3_0,u1_struct_0(esk4_0))),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_25]),c_0_28]),c_0_29])])).

cnf(c_0_56,negated_conjecture,
    ( esk2_3(esk3_0,esk4_0,k7_tmap_1(esk3_0,u1_struct_0(esk4_0))) = u1_struct_0(esk4_0)
    | k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_25]),c_0_28]),c_0_29])])).

fof(c_0_57,plain,(
    ! [X35,X36,X37,X38] :
      ( ~ v1_funct_1(X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | k2_partfun1(X35,X36,X37,X38) = k7_relat_1(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,plain,
    ( r1_tmap_1(X1,k6_tmap_1(X2,u1_struct_0(X1)),k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(X1)),k7_tmap_1(X2,u1_struct_0(X1)),X1),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_54]),c_0_25])).

cnf(c_0_60,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_62,plain,(
    ! [X17,X18,X19,X20] :
      ( v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | v2_struct_0(X18)
      | ~ v2_pre_topc(X18)
      | ~ l1_pre_topc(X18)
      | ~ v1_funct_1(X19)
      | ~ v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X18))
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X18))))
      | ~ m1_pre_topc(X20,X17)
      | k2_tmap_1(X17,X18,X19,X20) = k2_partfun1(u1_struct_0(X17),u1_struct_0(X18),X19,u1_struct_0(X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_63,plain,
    ( v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_25])).

cnf(c_0_64,negated_conjecture,
    ( r1_tmap_1(esk4_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),X1)
    | m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_38]),c_0_38]),c_0_28]),c_0_29]),c_0_30])]),c_0_32]),c_0_31])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_67,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),X1) = k7_relat_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),X1)
    | ~ v1_funct_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_43])).

fof(c_0_68,plain,(
    ! [X27,X28] :
      ( ( v1_funct_1(k9_tmap_1(X27,X28))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_pre_topc(X28,X27) )
      & ( v1_funct_2(k9_tmap_1(X27,X28),u1_struct_0(X27),u1_struct_0(k8_tmap_1(X27,X28)))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_pre_topc(X28,X27) )
      & ( m1_subset_1(k9_tmap_1(X27,X28),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(k8_tmap_1(X27,X28)))))
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_pre_topc(X28,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

cnf(c_0_69,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_28]),c_0_29]),c_0_30])]),c_0_32])).

cnf(c_0_71,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_28]),c_0_29]),c_0_30])]),c_0_32])).

cnf(c_0_72,negated_conjecture,
    ( ~ v2_struct_0(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_38]),c_0_28]),c_0_29]),c_0_30])]),c_0_32])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),X1) = k7_relat_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),X1)
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_48])])).

cnf(c_0_75,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_76,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_77,negated_conjecture,
    ( k2_tmap_1(X1,k8_tmap_1(esk3_0,esk4_0),X2,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(esk3_0),X2,u1_struct_0(X3))
    | v2_struct_0(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_36]),c_0_70]),c_0_71])]),c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_73])])).

cnf(c_0_79,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),X1) = k7_relat_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_73])])).

cnf(c_0_80,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),u1_struct_0(esk3_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_73])])).

fof(c_0_81,plain,(
    ! [X39,X40,X41,X42,X43,X44] :
      ( ( ~ r1_funct_2(X39,X40,X41,X42,X43,X44)
        | X43 = X44
        | v1_xboole_0(X40)
        | v1_xboole_0(X42)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X39,X40)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X41,X42)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( X43 != X44
        | r1_funct_2(X39,X40,X41,X42,X43,X44)
        | v1_xboole_0(X40)
        | v1_xboole_0(X42)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X39,X40)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X41,X42)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_82,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_83,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_28]),c_0_36]),c_0_29]),c_0_30])]),c_0_32])).

cnf(c_0_85,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_28]),c_0_29]),c_0_30])]),c_0_32])).

cnf(c_0_86,negated_conjecture,
    ( r1_tmap_1(esk4_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),esk4_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_38]),c_0_28]),c_0_29]),c_0_30])]),c_0_32]),c_0_31])).

cnf(c_0_87,negated_conjecture,
    ( k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),X1) = k7_relat_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79]),c_0_80]),c_0_48]),c_0_29]),c_0_30])]),c_0_32])).

cnf(c_0_88,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_89,plain,
    ( r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,u1_struct_0(X2))),k9_tmap_1(X1,X2),k7_tmap_1(X1,u1_struct_0(X2)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_82])]),c_0_25]),c_0_75]),c_0_76]),c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),k9_tmap_1(esk3_0,esk4_0),X1) = k7_relat_1(k9_tmap_1(esk3_0,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_84]),c_0_85])])).

cnf(c_0_91,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk3_0,esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_28]),c_0_36]),c_0_29]),c_0_30])]),c_0_32])).

cnf(c_0_92,negated_conjecture,
    ( r1_tmap_1(esk4_0,k8_tmap_1(esk3_0,esk4_0),k7_relat_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_28])])).

cnf(c_0_93,negated_conjecture,
    ( k7_relat_1(k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),u1_struct_0(X1)) = k2_tmap_1(esk3_0,esk3_0,k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_78]),c_0_79]),c_0_80]),c_0_48]),c_0_29]),c_0_30])]),c_0_32])).

cnf(c_0_94,negated_conjecture,
    ( X1 = k7_tmap_1(esk3_0,u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(X2)
    | ~ r1_funct_2(X3,X2,u1_struct_0(esk3_0),u1_struct_0(esk3_0),X1,k7_tmap_1(esk3_0,u1_struct_0(esk4_0)))
    | ~ v1_funct_2(X1,X3,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_78]),c_0_80]),c_0_48])])).

cnf(c_0_95,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),k9_tmap_1(esk3_0,esk4_0),k7_tmap_1(esk3_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_28]),c_0_36]),c_0_38]),c_0_36]),c_0_29]),c_0_30])]),c_0_32])).

cnf(c_0_96,negated_conjecture,
    ( k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),X1) = k7_relat_1(k9_tmap_1(esk3_0,esk4_0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_84]),c_0_90]),c_0_91]),c_0_85]),c_0_29]),c_0_30])]),c_0_32])).

cnf(c_0_97,negated_conjecture,
    ( r1_tmap_1(esk4_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,esk3_0,k7_tmap_1(esk3_0,u1_struct_0(esk4_0)),esk4_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_28])])).

cnf(c_0_98,negated_conjecture,
    ( k7_tmap_1(esk3_0,u1_struct_0(esk4_0)) = k9_tmap_1(esk3_0,esk4_0)
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_91]),c_0_85]),c_0_84])])).

cnf(c_0_99,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,k8_tmap_1(esk3_0,esk4_0),k7_relat_1(k9_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_96]),c_0_28])])).

cnf(c_0_100,negated_conjecture,
    ( k7_relat_1(k9_tmap_1(esk3_0,esk4_0),u1_struct_0(X1)) = k2_tmap_1(esk3_0,esk3_0,k9_tmap_1(esk3_0,esk4_0),X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_84]),c_0_90]),c_0_91]),c_0_85]),c_0_29]),c_0_30])]),c_0_32])).

fof(c_0_101,plain,(
    ! [X32] :
      ( v2_struct_0(X32)
      | ~ l1_struct_0(X32)
      | ~ v1_xboole_0(u1_struct_0(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_102,negated_conjecture,
    ( r1_tmap_1(esk4_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,esk3_0,k9_tmap_1(esk3_0,esk4_0),esk4_0),X1)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,esk3_0,k9_tmap_1(esk3_0,esk4_0),esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_28])])).

cnf(c_0_104,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_105,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_65]),c_0_103])).

fof(c_0_106,plain,(
    ! [X29] :
      ( ~ l1_pre_topc(X29)
      | l1_struct_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_107,negated_conjecture,
    ( ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_32])).

cnf(c_0_108,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_109,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_29])]),
    [proof]).

%------------------------------------------------------------------------------
