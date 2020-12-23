%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:26 EST 2020

% Result     : CounterSatisfiable 0.15s
% Output     : Saturation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 302 expanded)
%              Number of clauses        :   55 ( 121 expanded)
%              Number of leaves         :   15 (  86 expanded)
%              Depth                    :    5
%              Number of atoms          :  731 (2986 expanded)
%              Number of equality atoms :   54 ( 257 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal clause size      :  103 (   6 average)
%              Maximal term depth       :    5 (   1 average)

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

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t112_tmap_1,axiom,(
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
               => ( v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3))
                  & v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))
                  & v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X3,k6_tmap_1(X1,X2))
                  & m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_tmap_1)).

fof(d10_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).

fof(t55_tmap_1,axiom,(
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
             => ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & v5_pre_topc(X3,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => r1_tmap_1(X1,X2,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

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

fof(t117_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(X1),k9_tmap_1(X1,X2),k3_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_tmap_1)).

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

fof(fc5_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( ~ v2_struct_0(k8_tmap_1(X1,X2))
        & v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_tmap_1)).

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

fof(c_0_15,plain,(
    ! [X21,X22,X23,X24] :
      ( ( X23 != k8_tmap_1(X21,X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))
        | X24 != u1_struct_0(X22)
        | X23 = k6_tmap_1(X21,X24)
        | ~ v1_pre_topc(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(esk1_3(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X21)))
        | X23 = k8_tmap_1(X21,X22)
        | ~ v1_pre_topc(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( esk1_3(X21,X22,X23) = u1_struct_0(X22)
        | X23 = k8_tmap_1(X21,X22)
        | ~ v1_pre_topc(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( X23 != k6_tmap_1(X21,esk1_3(X21,X22,X23))
        | X23 = k8_tmap_1(X21,X22)
        | ~ v1_pre_topc(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).

fof(c_0_16,plain,(
    ! [X26,X27] :
      ( ( v1_pre_topc(k8_tmap_1(X26,X27))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_pre_topc(X27,X26) )
      & ( v2_pre_topc(k8_tmap_1(X26,X27))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_pre_topc(X27,X26) )
      & ( l1_pre_topc(k8_tmap_1(X26,X27))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_pre_topc(X27,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

fof(c_0_17,negated_conjecture,(
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

cnf(c_0_18,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_19,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_20,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_21,plain,
    ( v1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

fof(c_0_22,plain,(
    ! [X37,X38] :
      ( ~ l1_pre_topc(X37)
      | ~ m1_pre_topc(X38,X37)
      | m1_subset_1(u1_struct_0(X38),k1_zfmisc_1(u1_struct_0(X37))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_23,plain,(
    ! [X32,X33,X34] :
      ( ( v1_funct_1(k2_tmap_1(X32,k6_tmap_1(X32,X33),k7_tmap_1(X32,X33),X34))
        | u1_struct_0(X34) != X33
        | v2_struct_0(X34)
        | ~ m1_pre_topc(X34,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( v1_funct_2(k2_tmap_1(X32,k6_tmap_1(X32,X33),k7_tmap_1(X32,X33),X34),u1_struct_0(X34),u1_struct_0(k6_tmap_1(X32,X33)))
        | u1_struct_0(X34) != X33
        | v2_struct_0(X34)
        | ~ m1_pre_topc(X34,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( v5_pre_topc(k2_tmap_1(X32,k6_tmap_1(X32,X33),k7_tmap_1(X32,X33),X34),X34,k6_tmap_1(X32,X33))
        | u1_struct_0(X34) != X33
        | v2_struct_0(X34)
        | ~ m1_pre_topc(X34,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( m1_subset_1(k2_tmap_1(X32,k6_tmap_1(X32,X33),k7_tmap_1(X32,X33),X34),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(k6_tmap_1(X32,X33)))))
        | u1_struct_0(X34) != X33
        | v2_struct_0(X34)
        | ~ m1_pre_topc(X34,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t112_tmap_1])])])])])).

fof(c_0_24,plain,(
    ! [X19,X20] :
      ( v2_struct_0(X19)
      | ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | k7_tmap_1(X19,X20) = k6_partfun1(u1_struct_0(X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).

fof(c_0_25,plain,(
    ! [X39,X40,X41,X42] :
      ( ( ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))
        | ~ v5_pre_topc(X41,X39,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))
        | ~ m1_subset_1(X42,u1_struct_0(X39))
        | r1_tmap_1(X39,X40,X41,X42)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( v1_funct_1(X41)
        | m1_subset_1(esk2_3(X39,X40,X41),u1_struct_0(X39))
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))
        | m1_subset_1(esk2_3(X39,X40,X41),u1_struct_0(X39))
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( v5_pre_topc(X41,X39,X40)
        | m1_subset_1(esk2_3(X39,X40,X41),u1_struct_0(X39))
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))
        | m1_subset_1(esk2_3(X39,X40,X41),u1_struct_0(X39))
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( v1_funct_1(X41)
        | ~ r1_tmap_1(X39,X40,X41,esk2_3(X39,X40,X41))
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))
        | ~ r1_tmap_1(X39,X40,X41,esk2_3(X39,X40,X41))
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( v5_pre_topc(X41,X39,X40)
        | ~ r1_tmap_1(X39,X40,X41,esk2_3(X39,X40,X41))
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))
        | ~ r1_tmap_1(X39,X40,X41,esk2_3(X39,X40,X41))
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_tmap_1])])])])])])).

fof(c_0_26,plain,(
    ! [X10,X11] :
      ( ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(X11,X10)
      | l1_pre_topc(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & ~ r1_tmap_1(esk4_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_28,plain,(
    ! [X7,X8] :
      ( ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(X8,X7)
      | v2_pre_topc(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_29,plain,
    ( k8_tmap_1(X1,X2) = k6_tmap_1(X1,X3)
    | v2_struct_0(X1)
    | X3 != u1_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_18]),c_0_19]),c_0_20]),c_0_21]),
    [final]).

cnf(c_0_30,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_31,plain,
    ( m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | u1_struct_0(X3) != X2
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_24]),
    [final]).

cnf(c_0_33,plain,
    ( v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | u1_struct_0(X3) != X2
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_34,plain,
    ( v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X3,k6_tmap_1(X1,X2))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | u1_struct_0(X3) != X2
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

fof(c_0_35,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r1_funct_2(X13,X14,X15,X16,X17,X18)
        | X17 = X18
        | v1_xboole_0(X14)
        | v1_xboole_0(X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X13,X14)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( X17 != X18
        | r1_funct_2(X13,X14,X15,X16,X17,X18)
        | v1_xboole_0(X14)
        | v1_xboole_0(X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X13,X14)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

fof(c_0_36,plain,(
    ! [X35,X36] :
      ( v2_struct_0(X35)
      | ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | v2_struct_0(X36)
      | ~ m1_pre_topc(X36,X35)
      | r1_funct_2(u1_struct_0(X35),u1_struct_0(k8_tmap_1(X35,X36)),u1_struct_0(X35),u1_struct_0(X35),k9_tmap_1(X35,X36),k3_struct_0(X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_tmap_1])])])])).

fof(c_0_37,plain,(
    ! [X28,X29] :
      ( ( v1_funct_1(k9_tmap_1(X28,X29))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_pre_topc(X29,X28) )
      & ( v1_funct_2(k9_tmap_1(X28,X29),u1_struct_0(X28),u1_struct_0(k8_tmap_1(X28,X29)))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_pre_topc(X29,X28) )
      & ( m1_subset_1(k9_tmap_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(k8_tmap_1(X28,X29)))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_pre_topc(X29,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

cnf(c_0_38,plain,
    ( v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | u1_struct_0(X3) != X2
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_39,plain,
    ( r1_tmap_1(X2,X3,X1,X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_41,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_43,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_45,plain,
    ( k6_tmap_1(X1,u1_struct_0(X2)) = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_29]),c_0_30]),
    [final]).

cnf(c_0_46,plain,
    ( m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k6_partfun1(u1_struct_0(X1)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | u1_struct_0(X3) != X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32]),
    [final]).

cnf(c_0_47,plain,
    ( v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,X2),k6_partfun1(u1_struct_0(X1)),X3),u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | u1_struct_0(X3) != X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_32]),
    [final]).

cnf(c_0_48,plain,
    ( v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k6_partfun1(u1_struct_0(X1)),X3),X3,k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | u1_struct_0(X3) != X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_32]),
    [final]).

cnf(c_0_49,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(X1),k9_tmap_1(X1,X2),k3_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36]),
    [final]).

cnf(c_0_51,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37]),
    [final]).

cnf(c_0_52,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37]),
    [final]).

cnf(c_0_53,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37]),
    [final]).

cnf(c_0_54,plain,
    ( v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k6_partfun1(u1_struct_0(X1)),X3))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | u1_struct_0(X3) != X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_32]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_56,plain,
    ( v2_struct_0(X3)
    | v2_struct_0(X2)
    | r1_tmap_1(X2,X3,X1,X4)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X1)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(cn,[status(thm)],[c_0_39]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_41]),c_0_42]),c_0_44])]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_61,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_62,plain,
    ( X1 = k8_tmap_1(X2,X3)
    | v2_struct_0(X2)
    | X1 != k6_tmap_1(X2,esk1_3(X2,X3,X1))
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_63,plain,
    ( esk1_3(X1,X2,X3) = u1_struct_0(X2)
    | X3 = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

fof(c_0_64,plain,(
    ! [X30,X31] :
      ( ( ~ v2_struct_0(k8_tmap_1(X30,X31))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_pre_topc(X31,X30) )
      & ( v1_pre_topc(k8_tmap_1(X30,X31))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_pre_topc(X31,X30) )
      & ( v2_pre_topc(k8_tmap_1(X30,X31))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_pre_topc(X31,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_tmap_1])])])])).

fof(c_0_65,plain,(
    ! [X12] :
      ( v2_struct_0(X12)
      | ~ l1_struct_0(X12)
      | ~ v1_xboole_0(u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_66,plain,(
    ! [X9] :
      ( ~ l1_pre_topc(X9)
      | l1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_67,plain,
    ( m1_subset_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k7_tmap_1(X1,u1_struct_0(X2)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | u1_struct_0(X3) != u1_struct_0(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_45]),c_0_30]),
    [final]).

cnf(c_0_68,plain,
    ( m1_subset_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k6_partfun1(u1_struct_0(X1)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | u1_struct_0(X3) != u1_struct_0(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_45]),c_0_30]),
    [final]).

cnf(c_0_69,plain,
    ( v1_funct_2(k2_tmap_1(X1,k8_tmap_1(X1,X2),k7_tmap_1(X1,u1_struct_0(X2)),X3),u1_struct_0(X3),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | u1_struct_0(X3) != u1_struct_0(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_45]),c_0_30]),
    [final]).

cnf(c_0_70,plain,
    ( v5_pre_topc(k2_tmap_1(X1,k8_tmap_1(X1,X2),k7_tmap_1(X1,u1_struct_0(X2)),X3),X3,k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | u1_struct_0(X3) != u1_struct_0(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_45]),c_0_30]),
    [final]).

cnf(c_0_71,plain,
    ( v1_funct_2(k2_tmap_1(X1,k8_tmap_1(X1,X2),k6_partfun1(u1_struct_0(X1)),X3),u1_struct_0(X3),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | u1_struct_0(X3) != u1_struct_0(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_45]),c_0_30]),
    [final]).

cnf(c_0_72,plain,
    ( v5_pre_topc(k2_tmap_1(X1,k8_tmap_1(X1,X2),k6_partfun1(u1_struct_0(X1)),X3),X3,k8_tmap_1(X1,X2))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | u1_struct_0(X3) != u1_struct_0(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_45]),c_0_30]),
    [final]).

cnf(c_0_73,plain,
    ( k9_tmap_1(X1,X2) = k3_struct_0(X1)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X1,X2)))
    | v1_xboole_0(u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(k3_struct_0(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ v1_funct_2(k3_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1))
    | ~ v1_funct_1(k3_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52]),c_0_53]),
    [final]).

cnf(c_0_74,plain,
    ( v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k7_tmap_1(X1,u1_struct_0(X2)),X3))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | u1_struct_0(X3) != u1_struct_0(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_45]),c_0_30]),
    [final]).

cnf(c_0_75,plain,
    ( v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k6_partfun1(u1_struct_0(X1)),X3))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | u1_struct_0(X3) != u1_struct_0(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_45]),c_0_30]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk3_0,esk4_0))
    | ~ v5_pre_topc(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),esk4_0,k8_tmap_1(esk3_0,esk4_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0))
    | ~ l1_pre_topc(k8_tmap_1(esk3_0,esk4_0))
    | ~ v2_pre_topc(k8_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_58]),c_0_59])]),c_0_60]),
    [final]).

cnf(c_0_77,plain,
    ( v5_pre_topc(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X2,X3,X1,esk2_3(X2,X3,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25]),
    [final]).

cnf(c_0_78,plain,
    ( v5_pre_topc(X1,X2,X3)
    | m1_subset_1(esk2_3(X2,X3,X1),u1_struct_0(X2))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25]),
    [final]).

cnf(c_0_79,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | X3 = k8_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_80,plain,
    ( r1_funct_2(X1,X2,X3,X4,X5,X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X5,X3,X4)
    | ~ v1_funct_2(X5,X1,X2)
    | ~ v1_funct_1(X5) ),
    inference(er,[status(thm)],[c_0_61]),
    [final]).

cnf(c_0_81,plain,
    ( X1 = k8_tmap_1(X2,X3)
    | v2_struct_0(X2)
    | k6_tmap_1(X2,u1_struct_0(X3)) != X1
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63]),
    [final]).

cnf(c_0_82,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k8_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64]),
    [final]).

cnf(c_0_83,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65]),
    [final]).

cnf(c_0_84,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66]),
    [final]).

cnf(c_0_85,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:38:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.15/0.39  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.15/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.15/0.39  #
% 0.15/0.39  # Preprocessing time       : 0.030 s
% 0.15/0.39  # Presaturation interreduction done
% 0.15/0.39  
% 0.15/0.39  # No proof found!
% 0.15/0.39  # SZS status CounterSatisfiable
% 0.15/0.39  # SZS output start Saturation
% 0.15/0.39  fof(d11_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(((v1_pre_topc(X3)&v2_pre_topc(X3))&l1_pre_topc(X3))=>(X3=k8_tmap_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(X4=u1_struct_0(X2)=>X3=k6_tmap_1(X1,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_tmap_1)).
% 0.15/0.39  fof(dt_k8_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_pre_topc(k8_tmap_1(X1,X2))&v2_pre_topc(k8_tmap_1(X1,X2)))&l1_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 0.15/0.39  fof(t119_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>r1_tmap_1(X2,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_tmap_1)).
% 0.15/0.39  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.15/0.39  fof(t112_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(u1_struct_0(X3)=X2=>(((v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3))&v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2))))&v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X3,k6_tmap_1(X1,X2)))&m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_tmap_1)).
% 0.15/0.39  fof(d10_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_tmap_1)).
% 0.15/0.39  fof(t55_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>r1_tmap_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tmap_1)).
% 0.15/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.15/0.39  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.15/0.39  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 0.15/0.39  fof(t117_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(X1),k9_tmap_1(X1,X2),k3_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_tmap_1)).
% 0.15/0.39  fof(dt_k9_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k9_tmap_1(X1,X2))&v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))&m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_tmap_1)).
% 0.15/0.39  fof(fc5_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((~(v2_struct_0(k8_tmap_1(X1,X2)))&v1_pre_topc(k8_tmap_1(X1,X2)))&v2_pre_topc(k8_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_tmap_1)).
% 0.15/0.39  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.15/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.15/0.39  fof(c_0_15, plain, ![X21, X22, X23, X24]:((X23!=k8_tmap_1(X21,X22)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X21)))|(X24!=u1_struct_0(X22)|X23=k6_tmap_1(X21,X24)))|(~v1_pre_topc(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23))|~m1_pre_topc(X22,X21)|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&((m1_subset_1(esk1_3(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X21)))|X23=k8_tmap_1(X21,X22)|(~v1_pre_topc(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23))|~m1_pre_topc(X22,X21)|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&((esk1_3(X21,X22,X23)=u1_struct_0(X22)|X23=k8_tmap_1(X21,X22)|(~v1_pre_topc(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23))|~m1_pre_topc(X22,X21)|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(X23!=k6_tmap_1(X21,esk1_3(X21,X22,X23))|X23=k8_tmap_1(X21,X22)|(~v1_pre_topc(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23))|~m1_pre_topc(X22,X21)|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_tmap_1])])])])])])).
% 0.15/0.39  fof(c_0_16, plain, ![X26, X27]:(((v1_pre_topc(k8_tmap_1(X26,X27))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_pre_topc(X27,X26)))&(v2_pre_topc(k8_tmap_1(X26,X27))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_pre_topc(X27,X26))))&(l1_pre_topc(k8_tmap_1(X26,X27))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_pre_topc(X27,X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).
% 0.15/0.39  fof(c_0_17, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>r1_tmap_1(X2,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X3))))), inference(assume_negation,[status(cth)],[t119_tmap_1])).
% 0.15/0.39  cnf(c_0_18, plain, (X1=k6_tmap_1(X2,X4)|v2_struct_0(X2)|X1!=k8_tmap_1(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|X4!=u1_struct_0(X3)|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.15/0.39  cnf(c_0_19, plain, (v2_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.15/0.39  cnf(c_0_20, plain, (l1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.15/0.39  cnf(c_0_21, plain, (v1_pre_topc(k8_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.15/0.39  fof(c_0_22, plain, ![X37, X38]:(~l1_pre_topc(X37)|(~m1_pre_topc(X38,X37)|m1_subset_1(u1_struct_0(X38),k1_zfmisc_1(u1_struct_0(X37))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.15/0.39  fof(c_0_23, plain, ![X32, X33, X34]:((((v1_funct_1(k2_tmap_1(X32,k6_tmap_1(X32,X33),k7_tmap_1(X32,X33),X34))|u1_struct_0(X34)!=X33|(v2_struct_0(X34)|~m1_pre_topc(X34,X32))|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))&(v1_funct_2(k2_tmap_1(X32,k6_tmap_1(X32,X33),k7_tmap_1(X32,X33),X34),u1_struct_0(X34),u1_struct_0(k6_tmap_1(X32,X33)))|u1_struct_0(X34)!=X33|(v2_struct_0(X34)|~m1_pre_topc(X34,X32))|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32))))&(v5_pre_topc(k2_tmap_1(X32,k6_tmap_1(X32,X33),k7_tmap_1(X32,X33),X34),X34,k6_tmap_1(X32,X33))|u1_struct_0(X34)!=X33|(v2_struct_0(X34)|~m1_pre_topc(X34,X32))|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32))))&(m1_subset_1(k2_tmap_1(X32,k6_tmap_1(X32,X33),k7_tmap_1(X32,X33),X34),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(k6_tmap_1(X32,X33)))))|u1_struct_0(X34)!=X33|(v2_struct_0(X34)|~m1_pre_topc(X34,X32))|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t112_tmap_1])])])])])).
% 0.15/0.39  fof(c_0_24, plain, ![X19, X20]:(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|k7_tmap_1(X19,X20)=k6_partfun1(u1_struct_0(X19)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).
% 0.15/0.39  fof(c_0_25, plain, ![X39, X40, X41, X42]:((~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))|~v5_pre_topc(X41,X39,X40)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))|(~m1_subset_1(X42,u1_struct_0(X39))|r1_tmap_1(X39,X40,X41,X42))|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40)))))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))&(((((v1_funct_1(X41)|m1_subset_1(esk2_3(X39,X40,X41),u1_struct_0(X39))|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40)))))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))&(v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))|m1_subset_1(esk2_3(X39,X40,X41),u1_struct_0(X39))|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40)))))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))&(v5_pre_topc(X41,X39,X40)|m1_subset_1(esk2_3(X39,X40,X41),u1_struct_0(X39))|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40)))))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))&(m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))|m1_subset_1(esk2_3(X39,X40,X41),u1_struct_0(X39))|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40)))))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))&((((v1_funct_1(X41)|~r1_tmap_1(X39,X40,X41,esk2_3(X39,X40,X41))|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40)))))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))&(v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))|~r1_tmap_1(X39,X40,X41,esk2_3(X39,X40,X41))|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40)))))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))&(v5_pre_topc(X41,X39,X40)|~r1_tmap_1(X39,X40,X41,esk2_3(X39,X40,X41))|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40)))))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))&(m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40))))|~r1_tmap_1(X39,X40,X41,esk2_3(X39,X40,X41))|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X40))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X40)))))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_tmap_1])])])])])])).
% 0.15/0.39  fof(c_0_26, plain, ![X10, X11]:(~l1_pre_topc(X10)|(~m1_pre_topc(X11,X10)|l1_pre_topc(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.15/0.39  fof(c_0_27, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&~r1_tmap_1(esk4_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.15/0.39  fof(c_0_28, plain, ![X7, X8]:(~v2_pre_topc(X7)|~l1_pre_topc(X7)|(~m1_pre_topc(X8,X7)|v2_pre_topc(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.15/0.39  cnf(c_0_29, plain, (k8_tmap_1(X1,X2)=k6_tmap_1(X1,X3)|v2_struct_0(X1)|X3!=u1_struct_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_18]), c_0_19]), c_0_20]), c_0_21]), ['final']).
% 0.15/0.39  cnf(c_0_30, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.15/0.39  cnf(c_0_31, plain, (m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X3)|v2_struct_0(X1)|u1_struct_0(X3)!=X2|~m1_pre_topc(X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.15/0.39  cnf(c_0_32, plain, (v2_struct_0(X1)|k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_24]), ['final']).
% 0.15/0.39  cnf(c_0_33, plain, (v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X3)|v2_struct_0(X1)|u1_struct_0(X3)!=X2|~m1_pre_topc(X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.15/0.39  cnf(c_0_34, plain, (v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X3,k6_tmap_1(X1,X2))|v2_struct_0(X3)|v2_struct_0(X1)|u1_struct_0(X3)!=X2|~m1_pre_topc(X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.15/0.39  fof(c_0_35, plain, ![X13, X14, X15, X16, X17, X18]:((~r1_funct_2(X13,X14,X15,X16,X17,X18)|X17=X18|(v1_xboole_0(X14)|v1_xboole_0(X16)|~v1_funct_1(X17)|~v1_funct_2(X17,X13,X14)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|~v1_funct_1(X18)|~v1_funct_2(X18,X15,X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))))&(X17!=X18|r1_funct_2(X13,X14,X15,X16,X17,X18)|(v1_xboole_0(X14)|v1_xboole_0(X16)|~v1_funct_1(X17)|~v1_funct_2(X17,X13,X14)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|~v1_funct_1(X18)|~v1_funct_2(X18,X15,X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 0.15/0.39  fof(c_0_36, plain, ![X35, X36]:(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|(v2_struct_0(X36)|~m1_pre_topc(X36,X35)|r1_funct_2(u1_struct_0(X35),u1_struct_0(k8_tmap_1(X35,X36)),u1_struct_0(X35),u1_struct_0(X35),k9_tmap_1(X35,X36),k3_struct_0(X35)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_tmap_1])])])])).
% 0.15/0.39  fof(c_0_37, plain, ![X28, X29]:(((v1_funct_1(k9_tmap_1(X28,X29))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|~m1_pre_topc(X29,X28)))&(v1_funct_2(k9_tmap_1(X28,X29),u1_struct_0(X28),u1_struct_0(k8_tmap_1(X28,X29)))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|~m1_pre_topc(X29,X28))))&(m1_subset_1(k9_tmap_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(k8_tmap_1(X28,X29)))))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|~m1_pre_topc(X29,X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).
% 0.15/0.39  cnf(c_0_38, plain, (v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3))|v2_struct_0(X3)|v2_struct_0(X1)|u1_struct_0(X3)!=X2|~m1_pre_topc(X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.15/0.39  cnf(c_0_39, plain, (r1_tmap_1(X2,X3,X1,X4)|v2_struct_0(X3)|v2_struct_0(X2)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~m1_subset_1(X4,u1_struct_0(X2))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.15/0.39  cnf(c_0_40, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.15/0.39  cnf(c_0_41, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.15/0.39  cnf(c_0_42, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.15/0.39  cnf(c_0_43, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28]), ['final']).
% 0.15/0.39  cnf(c_0_44, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.15/0.39  cnf(c_0_45, plain, (k6_tmap_1(X1,u1_struct_0(X2))=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_29]), c_0_30]), ['final']).
% 0.15/0.39  cnf(c_0_46, plain, (m1_subset_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k6_partfun1(u1_struct_0(X1)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X1)|v2_struct_0(X3)|u1_struct_0(X3)!=X2|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X3,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_31, c_0_32]), ['final']).
% 0.15/0.39  cnf(c_0_47, plain, (v1_funct_2(k2_tmap_1(X1,k6_tmap_1(X1,X2),k6_partfun1(u1_struct_0(X1)),X3),u1_struct_0(X3),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X1)|v2_struct_0(X3)|u1_struct_0(X3)!=X2|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X3,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_33, c_0_32]), ['final']).
% 0.15/0.39  cnf(c_0_48, plain, (v5_pre_topc(k2_tmap_1(X1,k6_tmap_1(X1,X2),k6_partfun1(u1_struct_0(X1)),X3),X3,k6_tmap_1(X1,X2))|v2_struct_0(X1)|v2_struct_0(X3)|u1_struct_0(X3)!=X2|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X3,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_34, c_0_32]), ['final']).
% 0.15/0.39  cnf(c_0_49, plain, (X5=X6|v1_xboole_0(X2)|v1_xboole_0(X4)|~r1_funct_2(X1,X2,X3,X4,X5,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,X1,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.15/0.39  cnf(c_0_50, plain, (v2_struct_0(X1)|v2_struct_0(X2)|r1_funct_2(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)),u1_struct_0(X1),u1_struct_0(X1),k9_tmap_1(X1,X2),k3_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36]), ['final']).
% 0.15/0.39  cnf(c_0_51, plain, (v1_funct_1(k9_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37]), ['final']).
% 0.15/0.39  cnf(c_0_52, plain, (v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37]), ['final']).
% 0.15/0.39  cnf(c_0_53, plain, (m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37]), ['final']).
% 0.15/0.39  cnf(c_0_54, plain, (v1_funct_1(k2_tmap_1(X1,k6_tmap_1(X1,X2),k6_partfun1(u1_struct_0(X1)),X3))|v2_struct_0(X1)|v2_struct_0(X3)|u1_struct_0(X3)!=X2|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X3,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_38, c_0_32]), ['final']).
% 0.15/0.39  cnf(c_0_55, negated_conjecture, (~r1_tmap_1(esk4_0,k8_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.15/0.39  cnf(c_0_56, plain, (v2_struct_0(X3)|v2_struct_0(X2)|r1_tmap_1(X2,X3,X1,X4)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_1(X1)|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(cn,[status(thm)],[c_0_39]), ['final']).
% 0.15/0.39  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.15/0.39  cnf(c_0_58, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])]), ['final']).
% 0.15/0.39  cnf(c_0_59, negated_conjecture, (v2_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_41]), c_0_42]), c_0_44])]), ['final']).
% 0.15/0.39  cnf(c_0_60, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.15/0.39  cnf(c_0_61, plain, (r1_funct_2(X3,X4,X5,X6,X1,X2)|v1_xboole_0(X4)|v1_xboole_0(X6)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X5,X6)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.15/0.39  cnf(c_0_62, plain, (X1=k8_tmap_1(X2,X3)|v2_struct_0(X2)|X1!=k6_tmap_1(X2,esk1_3(X2,X3,X1))|~v1_pre_topc(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.15/0.39  cnf(c_0_63, plain, (esk1_3(X1,X2,X3)=u1_struct_0(X2)|X3=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_pre_topc(X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.15/0.39  fof(c_0_64, plain, ![X30, X31]:(((~v2_struct_0(k8_tmap_1(X30,X31))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|~m1_pre_topc(X31,X30)))&(v1_pre_topc(k8_tmap_1(X30,X31))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|~m1_pre_topc(X31,X30))))&(v2_pre_topc(k8_tmap_1(X30,X31))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|~m1_pre_topc(X31,X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_tmap_1])])])])).
% 0.15/0.39  fof(c_0_65, plain, ![X12]:(v2_struct_0(X12)|~l1_struct_0(X12)|~v1_xboole_0(u1_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.15/0.39  fof(c_0_66, plain, ![X9]:(~l1_pre_topc(X9)|l1_struct_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.15/0.39  cnf(c_0_67, plain, (m1_subset_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k7_tmap_1(X1,u1_struct_0(X2)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k8_tmap_1(X1,X2)))))|v2_struct_0(X1)|v2_struct_0(X3)|u1_struct_0(X3)!=u1_struct_0(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_45]), c_0_30]), ['final']).
% 0.15/0.39  cnf(c_0_68, plain, (m1_subset_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k6_partfun1(u1_struct_0(X1)),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(k8_tmap_1(X1,X2)))))|v2_struct_0(X3)|v2_struct_0(X1)|u1_struct_0(X3)!=u1_struct_0(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_45]), c_0_30]), ['final']).
% 0.15/0.39  cnf(c_0_69, plain, (v1_funct_2(k2_tmap_1(X1,k8_tmap_1(X1,X2),k7_tmap_1(X1,u1_struct_0(X2)),X3),u1_struct_0(X3),u1_struct_0(k8_tmap_1(X1,X2)))|v2_struct_0(X1)|v2_struct_0(X3)|u1_struct_0(X3)!=u1_struct_0(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_45]), c_0_30]), ['final']).
% 0.15/0.39  cnf(c_0_70, plain, (v5_pre_topc(k2_tmap_1(X1,k8_tmap_1(X1,X2),k7_tmap_1(X1,u1_struct_0(X2)),X3),X3,k8_tmap_1(X1,X2))|v2_struct_0(X1)|v2_struct_0(X3)|u1_struct_0(X3)!=u1_struct_0(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_45]), c_0_30]), ['final']).
% 0.15/0.39  cnf(c_0_71, plain, (v1_funct_2(k2_tmap_1(X1,k8_tmap_1(X1,X2),k6_partfun1(u1_struct_0(X1)),X3),u1_struct_0(X3),u1_struct_0(k8_tmap_1(X1,X2)))|v2_struct_0(X3)|v2_struct_0(X1)|u1_struct_0(X3)!=u1_struct_0(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_45]), c_0_30]), ['final']).
% 0.15/0.39  cnf(c_0_72, plain, (v5_pre_topc(k2_tmap_1(X1,k8_tmap_1(X1,X2),k6_partfun1(u1_struct_0(X1)),X3),X3,k8_tmap_1(X1,X2))|v2_struct_0(X3)|v2_struct_0(X1)|u1_struct_0(X3)!=u1_struct_0(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_45]), c_0_30]), ['final']).
% 0.15/0.39  cnf(c_0_73, plain, (k9_tmap_1(X1,X2)=k3_struct_0(X1)|v1_xboole_0(u1_struct_0(k8_tmap_1(X1,X2)))|v1_xboole_0(u1_struct_0(X1))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_subset_1(k3_struct_0(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~v1_funct_2(k3_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1))|~v1_funct_1(k3_struct_0(X1))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_52]), c_0_53]), ['final']).
% 0.15/0.39  cnf(c_0_74, plain, (v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k7_tmap_1(X1,u1_struct_0(X2)),X3))|v2_struct_0(X1)|v2_struct_0(X3)|u1_struct_0(X3)!=u1_struct_0(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_45]), c_0_30]), ['final']).
% 0.15/0.39  cnf(c_0_75, plain, (v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k6_partfun1(u1_struct_0(X1)),X3))|v2_struct_0(X3)|v2_struct_0(X1)|u1_struct_0(X3)!=u1_struct_0(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_45]), c_0_30]), ['final']).
% 0.15/0.39  cnf(c_0_76, negated_conjecture, (v2_struct_0(k8_tmap_1(esk3_0,esk4_0))|~v5_pre_topc(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),esk4_0,k8_tmap_1(esk3_0,esk4_0))|~m1_subset_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))))|~v1_funct_2(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(k8_tmap_1(esk3_0,esk4_0)))|~v1_funct_1(k2_tmap_1(esk3_0,k8_tmap_1(esk3_0,esk4_0),k9_tmap_1(esk3_0,esk4_0),esk4_0))|~l1_pre_topc(k8_tmap_1(esk3_0,esk4_0))|~v2_pre_topc(k8_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_58]), c_0_59])]), c_0_60]), ['final']).
% 0.15/0.39  cnf(c_0_77, plain, (v5_pre_topc(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X2,X3,X1,esk2_3(X2,X3,X1))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25]), ['final']).
% 0.15/0.39  cnf(c_0_78, plain, (v5_pre_topc(X1,X2,X3)|m1_subset_1(esk2_3(X2,X3,X1),u1_struct_0(X2))|v2_struct_0(X3)|v2_struct_0(X2)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25]), ['final']).
% 0.15/0.39  cnf(c_0_79, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|X3=k8_tmap_1(X1,X2)|v2_struct_0(X1)|~v1_pre_topc(X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.15/0.39  cnf(c_0_80, plain, (r1_funct_2(X1,X2,X3,X4,X5,X5)|v1_xboole_0(X4)|v1_xboole_0(X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(X5,X3,X4)|~v1_funct_2(X5,X1,X2)|~v1_funct_1(X5)), inference(er,[status(thm)],[c_0_61]), ['final']).
% 0.15/0.39  cnf(c_0_81, plain, (X1=k8_tmap_1(X2,X3)|v2_struct_0(X2)|k6_tmap_1(X2,u1_struct_0(X3))!=X1|~v1_pre_topc(X1)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_62, c_0_63]), ['final']).
% 0.15/0.39  cnf(c_0_82, plain, (v2_struct_0(X1)|~v2_struct_0(k8_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_64]), ['final']).
% 0.15/0.39  cnf(c_0_83, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_65]), ['final']).
% 0.15/0.39  cnf(c_0_84, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_66]), ['final']).
% 0.15/0.39  cnf(c_0_85, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.15/0.39  # SZS output end Saturation
% 0.15/0.39  # Proof object total steps             : 86
% 0.15/0.39  # Proof object clause steps            : 55
% 0.15/0.39  # Proof object formula steps           : 31
% 0.15/0.39  # Proof object conjectures             : 13
% 0.15/0.39  # Proof object clause conjectures      : 10
% 0.15/0.39  # Proof object formula conjectures     : 3
% 0.15/0.39  # Proof object initial clauses used    : 34
% 0.15/0.39  # Proof object initial formulas used   : 15
% 0.15/0.39  # Proof object generating inferences   : 19
% 0.15/0.39  # Proof object simplifying inferences  : 27
% 0.15/0.39  # Parsed axioms                        : 15
% 0.15/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.39  # Initial clauses                      : 42
% 0.15/0.39  # Removed in clause preprocessing      : 6
% 0.15/0.39  # Initial clauses in saturation        : 36
% 0.15/0.39  # Processed clauses                    : 102
% 0.15/0.39  # ...of these trivial                  : 0
% 0.15/0.39  # ...subsumed                          : 13
% 0.15/0.39  # ...remaining for further processing  : 89
% 0.15/0.39  # Other redundant clauses eliminated   : 1
% 0.15/0.39  # Clauses deleted for lack of memory   : 0
% 0.15/0.39  # Backward-subsumed                    : 1
% 0.15/0.39  # Backward-rewritten                   : 0
% 0.15/0.39  # Generated clauses                    : 34
% 0.15/0.39  # ...of the previous two non-trivial   : 32
% 0.15/0.39  # Contextual simplify-reflections      : 15
% 0.15/0.39  # Paramodulations                      : 30
% 0.15/0.39  # Factorizations                       : 0
% 0.15/0.39  # Equation resolutions                 : 4
% 0.15/0.39  # Propositional unsat checks           : 0
% 0.15/0.39  #    Propositional check models        : 0
% 0.15/0.39  #    Propositional check unsatisfiable : 0
% 0.15/0.39  #    Propositional clauses             : 0
% 0.15/0.39  #    Propositional clauses after purity: 0
% 0.15/0.39  #    Propositional unsat core size     : 0
% 0.15/0.39  #    Propositional preprocessing time  : 0.000
% 0.15/0.39  #    Propositional encoding time       : 0.000
% 0.15/0.39  #    Propositional solver time         : 0.000
% 0.15/0.39  #    Success case prop preproc time    : 0.000
% 0.15/0.39  #    Success case prop encoding time   : 0.000
% 0.15/0.39  #    Success case prop solver time     : 0.000
% 0.15/0.39  # Current number of processed clauses  : 53
% 0.15/0.39  #    Positive orientable unit clauses  : 6
% 0.15/0.39  #    Positive unorientable unit clauses: 0
% 0.15/0.39  #    Negative unit clauses             : 3
% 0.15/0.39  #    Non-unit-clauses                  : 44
% 0.15/0.39  # Current number of unprocessed clauses: 0
% 0.15/0.39  # ...number of literals in the above   : 0
% 0.15/0.39  # Current number of archived formulas  : 0
% 0.15/0.39  # Current number of archived clauses   : 35
% 0.15/0.39  # Clause-clause subsumption calls (NU) : 2701
% 0.15/0.39  # Rec. Clause-clause subsumption calls : 102
% 0.15/0.39  # Non-unit clause-clause subsumptions  : 29
% 0.15/0.39  # Unit Clause-clause subsumption calls : 4
% 0.15/0.39  # Rewrite failures with RHS unbound    : 0
% 0.15/0.39  # BW rewrite match attempts            : 0
% 0.15/0.39  # BW rewrite match successes           : 0
% 0.15/0.39  # Condensation attempts                : 0
% 0.15/0.39  # Condensation successes               : 0
% 0.15/0.39  # Termbank termtop insertions          : 7282
% 0.15/0.39  
% 0.15/0.39  # -------------------------------------------------
% 0.15/0.39  # User time                : 0.041 s
% 0.15/0.39  # System time              : 0.003 s
% 0.15/0.39  # Total time               : 0.044 s
% 0.15/0.39  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
