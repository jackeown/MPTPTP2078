%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:15 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 965 expanded)
%              Number of clauses        :   70 ( 336 expanded)
%              Number of leaves         :   15 ( 241 expanded)
%              Depth                    :   19
%              Number of atoms          :  485 (10049 expanded)
%              Number of equality atoms :   34 ( 498 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   25 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_tmap_1,conjecture,(
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
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) )
                     => ( ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X2))
                           => ( r2_hidden(X6,u1_struct_0(X3))
                             => k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                       => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d9_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r2_funct_2(X1,X2,X3,X4)
          <=> ! [X5] :
                ( m1_subset_1(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_2)).

fof(dt_k2_tmap_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        & l1_struct_0(X4) )
     => ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
        & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t72_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,X2)
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(t55_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_15,negated_conjecture,(
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
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) )
                       => ( ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                             => ( r2_hidden(X6,u1_struct_0(X3))
                               => k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                         => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_tmap_1])).

fof(c_0_16,plain,(
    ! [X35,X36] :
      ( ~ l1_pre_topc(X35)
      | ~ m1_pre_topc(X36,X35)
      | l1_pre_topc(X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_17,negated_conjecture,(
    ! [X54] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk3_0)
      & v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
      & v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      & ( ~ m1_subset_1(X54,u1_struct_0(esk3_0))
        | ~ r2_hidden(X54,u1_struct_0(esk4_0))
        | k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X54) = k1_funct_1(esk6_0,X54) )
      & ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])).

fof(c_0_18,plain,(
    ! [X16,X17,X18,X19,X20] :
      ( ( ~ r2_funct_2(X16,X17,X18,X19)
        | ~ m1_subset_1(X20,X16)
        | k1_funct_1(X18,X20) = k1_funct_1(X19,X20)
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X16,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( m1_subset_1(esk1_4(X16,X17,X18,X19),X16)
        | r2_funct_2(X16,X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X16,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( k1_funct_1(X18,esk1_4(X16,X17,X18,X19)) != k1_funct_1(X19,esk1_4(X16,X17,X18,X19))
        | r2_funct_2(X16,X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X16,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).

fof(c_0_19,plain,(
    ! [X45,X46,X47,X48] :
      ( ( v1_funct_1(k2_tmap_1(X45,X46,X47,X48))
        | ~ l1_struct_0(X45)
        | ~ l1_struct_0(X46)
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,u1_struct_0(X45),u1_struct_0(X46))
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X46))))
        | ~ l1_struct_0(X48) )
      & ( v1_funct_2(k2_tmap_1(X45,X46,X47,X48),u1_struct_0(X48),u1_struct_0(X46))
        | ~ l1_struct_0(X45)
        | ~ l1_struct_0(X46)
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,u1_struct_0(X45),u1_struct_0(X46))
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X46))))
        | ~ l1_struct_0(X48) )
      & ( m1_subset_1(k2_tmap_1(X45,X46,X47,X48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X48),u1_struct_0(X46))))
        | ~ l1_struct_0(X45)
        | ~ l1_struct_0(X46)
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,u1_struct_0(X45),u1_struct_0(X46))
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X46))))
        | ~ l1_struct_0(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

fof(c_0_20,plain,(
    ! [X34] :
      ( ~ l1_pre_topc(X34)
      | l1_struct_0(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_21,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X41,X42,X43,X44] :
      ( v2_struct_0(X41)
      | ~ v2_pre_topc(X41)
      | ~ l1_pre_topc(X41)
      | v2_struct_0(X42)
      | ~ v2_pre_topc(X42)
      | ~ l1_pre_topc(X42)
      | ~ v1_funct_1(X43)
      | ~ v1_funct_2(X43,u1_struct_0(X41),u1_struct_0(X42))
      | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X42))))
      | ~ m1_pre_topc(X44,X41)
      | k2_tmap_1(X41,X42,X43,X44) = k2_partfun1(u1_struct_0(X41),u1_struct_0(X42),X43,u1_struct_0(X44)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),X1)
    | r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_32,plain,(
    ! [X26,X27,X28,X29] :
      ( ~ v1_funct_1(X28)
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k2_partfun1(X26,X27,X28,X29) = k7_relat_1(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_33,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_41,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_relat_1(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_42,plain,(
    ! [X11,X12] : v1_relat_1(k2_zfmisc_1(X11,X12)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_43,plain,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,k2_tmap_1(X4,X2,X5,X1))
    | m1_subset_1(esk1_4(u1_struct_0(X1),u1_struct_0(X2),X3,k2_tmap_1(X4,X2,X5,X1)),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X4)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_45,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_31])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_49,plain,(
    ! [X13,X14,X15] :
      ( ~ v1_relat_1(X15)
      | ~ v1_funct_1(X15)
      | ~ r2_hidden(X13,X14)
      | k1_funct_1(k7_relat_1(X15,X14),X13) = k1_funct_1(X15,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_funct_1])])).

cnf(c_0_50,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_51,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X1)) = k2_tmap_1(esk3_0,esk2_0,esk5_0,X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36]),c_0_31]),c_0_23]),c_0_37]),c_0_38])]),c_0_39]),c_0_40])).

cnf(c_0_52,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_54,plain,(
    ! [X22,X23,X24,X25] :
      ( ( v1_funct_1(k2_partfun1(X22,X23,X24,X25))
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( m1_subset_1(k2_partfun1(X22,X23,X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

fof(c_0_55,plain,(
    ! [X38,X39,X40] :
      ( v2_struct_0(X38)
      | ~ l1_pre_topc(X38)
      | v2_struct_0(X39)
      | ~ m1_pre_topc(X39,X38)
      | ~ m1_subset_1(X40,u1_struct_0(X39))
      | m1_subset_1(X40,u1_struct_0(X38)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_56,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(X1,esk2_0,X2,esk4_0))
    | m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(X1,esk2_0,X2,esk4_0)),u1_struct_0(esk4_0))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46]),c_0_47]),c_0_48])])).

cnf(c_0_57,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

cnf(c_0_58,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( k7_relat_1(esk5_0,u1_struct_0(X1)) = k2_tmap_1(esk3_0,esk2_0,esk5_0,X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_38]),c_0_34])])).

cnf(c_0_60,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_34]),c_0_53])])).

cnf(c_0_61,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_62,plain,(
    ! [X7,X8] :
      ( ~ m1_subset_1(X7,X8)
      | v1_xboole_0(X8)
      | r2_hidden(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_63,plain,(
    ! [X30,X31,X32,X33] :
      ( v1_xboole_0(X30)
      | ~ v1_funct_1(X32)
      | ~ v1_funct_2(X32,X30,X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | ~ m1_subset_1(X33,X30)
      | k3_funct_2(X30,X31,X32,X33) = k1_funct_1(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_64,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_34]),c_0_57]),c_0_37]),c_0_38])])).

cnf(c_0_66,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_67,plain,
    ( r2_funct_2(X2,X3,X1,X4)
    | k1_funct_1(X1,esk1_4(X2,X3,X1,X4)) != k1_funct_1(X4,esk1_4(X2,X3,X1,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_68,negated_conjecture,
    ( k1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,X1),X2) = k1_funct_1(esk5_0,X2)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ r2_hidden(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_38]),c_0_60])])).

cnf(c_0_69,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,X1))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_51]),c_0_38]),c_0_34])])).

cnf(c_0_70,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_71,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(X1))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( r2_funct_2(X1,X2,X3,k2_tmap_1(esk3_0,esk2_0,esk5_0,X4))
    | k1_funct_1(X3,esk1_4(X1,X2,X3,k2_tmap_1(esk3_0,esk2_0,esk5_0,X4))) != k1_funct_1(esk5_0,esk1_4(X1,X2,X3,k2_tmap_1(esk3_0,esk2_0,esk5_0,X4)))
    | ~ m1_pre_topc(X4,esk3_0)
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,X4),X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ r2_hidden(esk1_4(X1,X2,X3,k2_tmap_1(esk3_0,esk2_0,esk5_0,X4)),u1_struct_0(X4))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | r2_hidden(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_65])).

cnf(c_0_75,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X1) = k1_funct_1(esk5_0,X1)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_34]),c_0_37]),c_0_38])])).

cnf(c_0_76,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_22]),c_0_23])]),c_0_40])).

cnf(c_0_77,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))) != k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_22]),c_0_47]),c_0_48]),c_0_44])])).

cnf(c_0_78,plain,
    ( k1_funct_1(X3,X5) = k1_funct_1(X4,X5)
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ m1_subset_1(X5,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_79,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X1) = k1_funct_1(esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_80,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))) = k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))) != k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_28]),c_0_45]),c_0_46]),c_0_57]),c_0_37]),c_0_38]),c_0_34])])).

cnf(c_0_82,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),X1,esk6_0)
    | m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),X1,esk6_0),u1_struct_0(esk4_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_44]),c_0_47]),c_0_48])])).

cnf(c_0_83,plain,
    ( k1_funct_1(X1,X2) = k1_funct_1(k2_tmap_1(X3,X4,X5,X6),X2)
    | ~ l1_struct_0(X6)
    | ~ l1_struct_0(X4)
    | ~ l1_struct_0(X3)
    | ~ r2_funct_2(u1_struct_0(X6),u1_struct_0(X4),X1,k2_tmap_1(X3,X4,X5,X6))
    | ~ v1_funct_2(X1,u1_struct_0(X6),u1_struct_0(X4))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X4))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X4))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
    | ~ m1_subset_1(X2,u1_struct_0(X6)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_84,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))) = k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r2_hidden(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_76])).

cnf(c_0_85,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))) != k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_26]),c_0_45]),c_0_46]),c_0_57]),c_0_37]),c_0_38]),c_0_34])])).

cnf(c_0_86,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0)
    | m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0),u1_struct_0(esk4_0))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_2(k2_tmap_1(X1,esk2_0,X2,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(X1,esk2_0,X2,esk4_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_26]),c_0_45]),c_0_46])])).

cnf(c_0_87,plain,
    ( r2_funct_2(X1,X2,X3,X4)
    | k1_funct_1(X3,esk1_4(X1,X2,X3,X4)) != k1_funct_1(k2_tmap_1(X5,X6,X7,X8),esk1_4(X1,X2,X3,X4))
    | ~ l1_struct_0(X8)
    | ~ l1_struct_0(X6)
    | ~ l1_struct_0(X5)
    | ~ r2_funct_2(u1_struct_0(X8),u1_struct_0(X6),X4,k2_tmap_1(X5,X6,X7,X8))
    | ~ v1_funct_2(X4,u1_struct_0(X8),u1_struct_0(X6))
    | ~ v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X6))
    | ~ v1_funct_2(X4,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X7)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X6))))
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
    | ~ m1_subset_1(esk1_4(X1,X2,X3,X4),u1_struct_0(X8))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_74]),c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0)
    | m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0),u1_struct_0(esk4_0))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(X1,esk2_0,X2,esk4_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_28]),c_0_45]),c_0_46])])).

cnf(c_0_90,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_91,negated_conjecture,
    ( r2_funct_2(X1,X2,X3,esk6_0)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | k1_funct_1(X3,esk1_4(X1,X2,X3,esk6_0)) != k1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk1_4(X1,X2,X3,esk6_0))
    | ~ v1_funct_2(esk6_0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(esk1_4(X1,X2,X3,esk6_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_45]),c_0_46]),c_0_57]),c_0_47]),c_0_37]),c_0_48]),c_0_38]),c_0_44]),c_0_34])])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0),u1_struct_0(esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_34]),c_0_57]),c_0_37]),c_0_38])]),c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_47]),c_0_44])]),c_0_90])).

cnf(c_0_94,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_27]),c_0_45]),c_0_46]),c_0_57]),c_0_37]),c_0_38]),c_0_34])])).

fof(c_0_95,plain,(
    ! [X37] :
      ( v2_struct_0(X37)
      | ~ l1_struct_0(X37)
      | ~ v1_xboole_0(u1_struct_0(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_96,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_28]),c_0_45]),c_0_46]),c_0_57]),c_0_37]),c_0_38]),c_0_34])])).

cnf(c_0_97,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_98,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_26]),c_0_45]),c_0_46]),c_0_57]),c_0_37]),c_0_38]),c_0_34])])).

cnf(c_0_99,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_45])]),c_0_66])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_99]),c_0_57])]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:26:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 3.89/4.09  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 3.89/4.09  # and selection function PSelectComplexExceptRRHorn.
% 3.89/4.09  #
% 3.89/4.09  # Preprocessing time       : 0.029 s
% 3.89/4.09  # Presaturation interreduction done
% 3.89/4.09  
% 3.89/4.09  # Proof found!
% 3.89/4.09  # SZS status Theorem
% 3.89/4.09  # SZS output start CNFRefutation
% 3.89/4.09  fof(t59_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>(![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(r2_hidden(X6,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6)=k1_funct_1(X5,X6)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tmap_1)).
% 3.89/4.09  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.89/4.09  fof(d9_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>![X5]:(m1_subset_1(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_2)).
% 3.89/4.09  fof(dt_k2_tmap_1, axiom, ![X1, X2, X3, X4]:((((((l1_struct_0(X1)&l1_struct_0(X2))&v1_funct_1(X3))&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))&l1_struct_0(X4))=>((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 3.89/4.09  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.89/4.09  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.89/4.09  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.89/4.09  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.89/4.09  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.89/4.09  fof(t72_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,X2)=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_funct_1)).
% 3.89/4.09  fof(dt_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(v1_funct_1(k2_partfun1(X1,X2,X3,X4))&m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 3.89/4.09  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 3.89/4.09  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.89/4.09  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.89/4.09  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.89/4.09  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>(![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(r2_hidden(X6,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6)=k1_funct_1(X5,X6)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)))))))), inference(assume_negation,[status(cth)],[t59_tmap_1])).
% 3.89/4.09  fof(c_0_16, plain, ![X35, X36]:(~l1_pre_topc(X35)|(~m1_pre_topc(X36,X35)|l1_pre_topc(X36))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 3.89/4.09  fof(c_0_17, negated_conjecture, ![X54]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))))&((~m1_subset_1(X54,u1_struct_0(esk3_0))|(~r2_hidden(X54,u1_struct_0(esk4_0))|k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X54)=k1_funct_1(esk6_0,X54)))&~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])).
% 3.89/4.09  fof(c_0_18, plain, ![X16, X17, X18, X19, X20]:((~r2_funct_2(X16,X17,X18,X19)|(~m1_subset_1(X20,X16)|k1_funct_1(X18,X20)=k1_funct_1(X19,X20))|(~v1_funct_1(X19)|~v1_funct_2(X19,X16,X17)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))|(~v1_funct_1(X18)|~v1_funct_2(X18,X16,X17)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))))&((m1_subset_1(esk1_4(X16,X17,X18,X19),X16)|r2_funct_2(X16,X17,X18,X19)|(~v1_funct_1(X19)|~v1_funct_2(X19,X16,X17)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))|(~v1_funct_1(X18)|~v1_funct_2(X18,X16,X17)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))))&(k1_funct_1(X18,esk1_4(X16,X17,X18,X19))!=k1_funct_1(X19,esk1_4(X16,X17,X18,X19))|r2_funct_2(X16,X17,X18,X19)|(~v1_funct_1(X19)|~v1_funct_2(X19,X16,X17)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))|(~v1_funct_1(X18)|~v1_funct_2(X18,X16,X17)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).
% 3.89/4.09  fof(c_0_19, plain, ![X45, X46, X47, X48]:(((v1_funct_1(k2_tmap_1(X45,X46,X47,X48))|(~l1_struct_0(X45)|~l1_struct_0(X46)|~v1_funct_1(X47)|~v1_funct_2(X47,u1_struct_0(X45),u1_struct_0(X46))|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X46))))|~l1_struct_0(X48)))&(v1_funct_2(k2_tmap_1(X45,X46,X47,X48),u1_struct_0(X48),u1_struct_0(X46))|(~l1_struct_0(X45)|~l1_struct_0(X46)|~v1_funct_1(X47)|~v1_funct_2(X47,u1_struct_0(X45),u1_struct_0(X46))|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X46))))|~l1_struct_0(X48))))&(m1_subset_1(k2_tmap_1(X45,X46,X47,X48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X48),u1_struct_0(X46))))|(~l1_struct_0(X45)|~l1_struct_0(X46)|~v1_funct_1(X47)|~v1_funct_2(X47,u1_struct_0(X45),u1_struct_0(X46))|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X46))))|~l1_struct_0(X48)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).
% 3.89/4.09  fof(c_0_20, plain, ![X34]:(~l1_pre_topc(X34)|l1_struct_0(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 3.89/4.09  cnf(c_0_21, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.89/4.09  cnf(c_0_22, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.89/4.09  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.89/4.09  fof(c_0_24, plain, ![X41, X42, X43, X44]:(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)|(~v1_funct_1(X43)|~v1_funct_2(X43,u1_struct_0(X41),u1_struct_0(X42))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X42))))|(~m1_pre_topc(X44,X41)|k2_tmap_1(X41,X42,X43,X44)=k2_partfun1(u1_struct_0(X41),u1_struct_0(X42),X43,u1_struct_0(X44)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 3.89/4.09  cnf(c_0_25, plain, (m1_subset_1(esk1_4(X1,X2,X3,X4),X1)|r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.89/4.09  cnf(c_0_26, plain, (m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.89/4.09  cnf(c_0_27, plain, (v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.89/4.09  cnf(c_0_28, plain, (v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.89/4.09  cnf(c_0_29, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.89/4.09  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 3.89/4.09  cnf(c_0_31, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.89/4.09  fof(c_0_32, plain, ![X26, X27, X28, X29]:(~v1_funct_1(X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k2_partfun1(X26,X27,X28,X29)=k7_relat_1(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 3.89/4.09  cnf(c_0_33, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 3.89/4.09  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.89/4.09  cnf(c_0_35, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.89/4.09  cnf(c_0_36, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.89/4.09  cnf(c_0_37, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.89/4.09  cnf(c_0_38, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.89/4.09  cnf(c_0_39, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.89/4.09  cnf(c_0_40, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.89/4.09  fof(c_0_41, plain, ![X9, X10]:(~v1_relat_1(X9)|(~m1_subset_1(X10,k1_zfmisc_1(X9))|v1_relat_1(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 3.89/4.09  fof(c_0_42, plain, ![X11, X12]:v1_relat_1(k2_zfmisc_1(X11,X12)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 3.89/4.09  cnf(c_0_43, plain, (r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,k2_tmap_1(X4,X2,X5,X1))|m1_subset_1(esk1_4(u1_struct_0(X1),u1_struct_0(X2),X3,k2_tmap_1(X4,X2,X5,X1)),u1_struct_0(X1))|~l1_struct_0(X1)|~l1_struct_0(X2)|~l1_struct_0(X4)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~v1_funct_1(X3)|~v1_funct_1(X5)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])).
% 3.89/4.09  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.89/4.09  cnf(c_0_45, negated_conjecture, (l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 3.89/4.09  cnf(c_0_46, negated_conjecture, (l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_31])).
% 3.89/4.09  cnf(c_0_47, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.89/4.09  cnf(c_0_48, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.89/4.09  fof(c_0_49, plain, ![X13, X14, X15]:(~v1_relat_1(X15)|~v1_funct_1(X15)|(~r2_hidden(X13,X14)|k1_funct_1(k7_relat_1(X15,X14),X13)=k1_funct_1(X15,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_funct_1])])).
% 3.89/4.09  cnf(c_0_50, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 3.89/4.09  cnf(c_0_51, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X1))=k2_tmap_1(esk3_0,esk2_0,esk5_0,X1)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36]), c_0_31]), c_0_23]), c_0_37]), c_0_38])]), c_0_39]), c_0_40])).
% 3.89/4.09  cnf(c_0_52, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 3.89/4.09  cnf(c_0_53, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 3.89/4.09  fof(c_0_54, plain, ![X22, X23, X24, X25]:((v1_funct_1(k2_partfun1(X22,X23,X24,X25))|(~v1_funct_1(X24)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))))&(m1_subset_1(k2_partfun1(X22,X23,X24,X25),k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|(~v1_funct_1(X24)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).
% 3.89/4.09  fof(c_0_55, plain, ![X38, X39, X40]:(v2_struct_0(X38)|~l1_pre_topc(X38)|(v2_struct_0(X39)|~m1_pre_topc(X39,X38)|(~m1_subset_1(X40,u1_struct_0(X39))|m1_subset_1(X40,u1_struct_0(X38))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 3.89/4.09  cnf(c_0_56, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(X1,esk2_0,X2,esk4_0))|m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(X1,esk2_0,X2,esk4_0)),u1_struct_0(esk4_0))|~l1_struct_0(X1)|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46]), c_0_47]), c_0_48])])).
% 3.89/4.09  cnf(c_0_57, negated_conjecture, (l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_29, c_0_23])).
% 3.89/4.09  cnf(c_0_58, plain, (k1_funct_1(k7_relat_1(X1,X3),X2)=k1_funct_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 3.89/4.09  cnf(c_0_59, negated_conjecture, (k7_relat_1(esk5_0,u1_struct_0(X1))=k2_tmap_1(esk3_0,esk2_0,esk5_0,X1)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_38]), c_0_34])])).
% 3.89/4.09  cnf(c_0_60, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_34]), c_0_53])])).
% 3.89/4.09  cnf(c_0_61, plain, (v1_funct_1(k2_partfun1(X1,X2,X3,X4))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 3.89/4.09  fof(c_0_62, plain, ![X7, X8]:(~m1_subset_1(X7,X8)|(v1_xboole_0(X8)|r2_hidden(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 3.89/4.09  fof(c_0_63, plain, ![X30, X31, X32, X33]:(v1_xboole_0(X30)|~v1_funct_1(X32)|~v1_funct_2(X32,X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|~m1_subset_1(X33,X30)|k3_funct_2(X30,X31,X32,X33)=k1_funct_1(X32,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 3.89/4.09  cnf(c_0_64, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 3.89/4.09  cnf(c_0_65, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_34]), c_0_57]), c_0_37]), c_0_38])])).
% 3.89/4.09  cnf(c_0_66, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.89/4.09  cnf(c_0_67, plain, (r2_funct_2(X2,X3,X1,X4)|k1_funct_1(X1,esk1_4(X2,X3,X1,X4))!=k1_funct_1(X4,esk1_4(X2,X3,X1,X4))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.89/4.09  cnf(c_0_68, negated_conjecture, (k1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,X1),X2)=k1_funct_1(esk5_0,X2)|~m1_pre_topc(X1,esk3_0)|~r2_hidden(X2,u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_38]), c_0_60])])).
% 3.89/4.09  cnf(c_0_69, negated_conjecture, (v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,X1))|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_51]), c_0_38]), c_0_34])])).
% 3.89/4.09  cnf(c_0_70, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 3.89/4.09  cnf(c_0_71, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 3.89/4.09  cnf(c_0_72, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(X1))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])).
% 3.89/4.09  cnf(c_0_73, negated_conjecture, (r2_funct_2(X1,X2,X3,k2_tmap_1(esk3_0,esk2_0,esk5_0,X4))|k1_funct_1(X3,esk1_4(X1,X2,X3,k2_tmap_1(esk3_0,esk2_0,esk5_0,X4)))!=k1_funct_1(esk5_0,esk1_4(X1,X2,X3,k2_tmap_1(esk3_0,esk2_0,esk5_0,X4)))|~m1_pre_topc(X4,esk3_0)|~v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,X4),X1,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~r2_hidden(esk1_4(X1,X2,X3,k2_tmap_1(esk3_0,esk2_0,esk5_0,X4)),u1_struct_0(X4))|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 3.89/4.09  cnf(c_0_74, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|r2_hidden(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_70, c_0_65])).
% 3.89/4.09  cnf(c_0_75, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X1)=k1_funct_1(esk5_0,X1)|v1_xboole_0(u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_34]), c_0_37]), c_0_38])])).
% 3.89/4.09  cnf(c_0_76, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_22]), c_0_23])]), c_0_40])).
% 3.89/4.09  cnf(c_0_77, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))|k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))!=k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))|~v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_22]), c_0_47]), c_0_48]), c_0_44])])).
% 3.89/4.09  cnf(c_0_78, plain, (k1_funct_1(X3,X5)=k1_funct_1(X4,X5)|~r2_funct_2(X1,X2,X3,X4)|~m1_subset_1(X5,X1)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.89/4.09  cnf(c_0_79, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X1)=k1_funct_1(esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.89/4.09  cnf(c_0_80, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))=k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 3.89/4.09  cnf(c_0_81, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))|k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))!=k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_28]), c_0_45]), c_0_46]), c_0_57]), c_0_37]), c_0_38]), c_0_34])])).
% 3.89/4.09  cnf(c_0_82, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),X1,esk6_0)|m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),X1,esk6_0),u1_struct_0(esk4_0))|~v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_44]), c_0_47]), c_0_48])])).
% 3.89/4.09  cnf(c_0_83, plain, (k1_funct_1(X1,X2)=k1_funct_1(k2_tmap_1(X3,X4,X5,X6),X2)|~l1_struct_0(X6)|~l1_struct_0(X4)|~l1_struct_0(X3)|~r2_funct_2(u1_struct_0(X6),u1_struct_0(X4),X1,k2_tmap_1(X3,X4,X5,X6))|~v1_funct_2(X1,u1_struct_0(X6),u1_struct_0(X4))|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X4))|~v1_funct_1(X1)|~v1_funct_1(X5)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X4))))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))|~m1_subset_1(X2,u1_struct_0(X6))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_26]), c_0_27]), c_0_28])).
% 3.89/4.09  cnf(c_0_84, negated_conjecture, (k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))=k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~r2_hidden(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_76])).
% 3.89/4.09  cnf(c_0_85, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))|k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))!=k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_26]), c_0_45]), c_0_46]), c_0_57]), c_0_37]), c_0_38]), c_0_34])])).
% 3.89/4.09  cnf(c_0_86, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0)|m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0),u1_struct_0(esk4_0))|~l1_struct_0(X1)|~v1_funct_2(k2_tmap_1(X1,esk2_0,X2,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(X1,esk2_0,X2,esk4_0))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_26]), c_0_45]), c_0_46])])).
% 3.89/4.09  cnf(c_0_87, plain, (r2_funct_2(X1,X2,X3,X4)|k1_funct_1(X3,esk1_4(X1,X2,X3,X4))!=k1_funct_1(k2_tmap_1(X5,X6,X7,X8),esk1_4(X1,X2,X3,X4))|~l1_struct_0(X8)|~l1_struct_0(X6)|~l1_struct_0(X5)|~r2_funct_2(u1_struct_0(X8),u1_struct_0(X6),X4,k2_tmap_1(X5,X6,X7,X8))|~v1_funct_2(X4,u1_struct_0(X8),u1_struct_0(X6))|~v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X6))|~v1_funct_2(X4,X1,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X4)|~v1_funct_1(X3)|~v1_funct_1(X7)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X6))))|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))|~m1_subset_1(esk1_4(X1,X2,X3,X4),u1_struct_0(X8))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_67, c_0_83])).
% 3.89/4.09  cnf(c_0_88, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_74]), c_0_85])).
% 3.89/4.09  cnf(c_0_89, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0)|m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0),u1_struct_0(esk4_0))|~l1_struct_0(X1)|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(X1,esk2_0,X2,esk4_0))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_28]), c_0_45]), c_0_46])])).
% 3.89/4.09  cnf(c_0_90, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.89/4.09  cnf(c_0_91, negated_conjecture, (r2_funct_2(X1,X2,X3,esk6_0)|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))|k1_funct_1(X3,esk1_4(X1,X2,X3,esk6_0))!=k1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk1_4(X1,X2,X3,esk6_0))|~v1_funct_2(esk6_0,X1,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~m1_subset_1(esk1_4(X1,X2,X3,esk6_0),u1_struct_0(esk4_0))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_45]), c_0_46]), c_0_57]), c_0_47]), c_0_37]), c_0_48]), c_0_38]), c_0_44]), c_0_34])])).
% 3.89/4.09  cnf(c_0_92, negated_conjecture, (m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0),u1_struct_0(esk4_0))|~v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_34]), c_0_57]), c_0_37]), c_0_38])]), c_0_90])).
% 3.89/4.09  cnf(c_0_93, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_47]), c_0_44])]), c_0_90])).
% 3.89/4.09  cnf(c_0_94, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))|~v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_27]), c_0_45]), c_0_46]), c_0_57]), c_0_37]), c_0_38]), c_0_34])])).
% 3.89/4.09  fof(c_0_95, plain, ![X37]:(v2_struct_0(X37)|~l1_struct_0(X37)|~v1_xboole_0(u1_struct_0(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 3.89/4.09  cnf(c_0_96, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_28]), c_0_45]), c_0_46]), c_0_57]), c_0_37]), c_0_38]), c_0_34])])).
% 3.89/4.09  cnf(c_0_97, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_95])).
% 3.89/4.09  cnf(c_0_98, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_26]), c_0_45]), c_0_46]), c_0_57]), c_0_37]), c_0_38]), c_0_34])])).
% 3.89/4.09  cnf(c_0_99, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_45])]), c_0_66])).
% 3.89/4.09  cnf(c_0_100, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_99]), c_0_57])]), c_0_40]), ['proof']).
% 3.89/4.09  # SZS output end CNFRefutation
% 3.89/4.09  # Proof object total steps             : 101
% 3.89/4.09  # Proof object clause steps            : 70
% 3.89/4.09  # Proof object formula steps           : 31
% 3.89/4.09  # Proof object conjectures             : 52
% 3.89/4.09  # Proof object clause conjectures      : 49
% 3.89/4.09  # Proof object formula conjectures     : 3
% 3.89/4.09  # Proof object initial clauses used    : 34
% 3.89/4.09  # Proof object initial formulas used   : 15
% 3.89/4.09  # Proof object generating inferences   : 36
% 3.89/4.09  # Proof object simplifying inferences  : 119
% 3.89/4.09  # Training examples: 0 positive, 0 negative
% 3.89/4.09  # Parsed axioms                        : 15
% 3.89/4.09  # Removed by relevancy pruning/SinE    : 0
% 3.89/4.09  # Initial clauses                      : 35
% 3.89/4.09  # Removed in clause preprocessing      : 0
% 3.89/4.09  # Initial clauses in saturation        : 35
% 3.89/4.09  # Processed clauses                    : 11024
% 3.89/4.09  # ...of these trivial                  : 11
% 3.89/4.09  # ...subsumed                          : 6809
% 3.89/4.09  # ...remaining for further processing  : 4204
% 3.89/4.09  # Other redundant clauses eliminated   : 0
% 3.89/4.09  # Clauses deleted for lack of memory   : 0
% 3.89/4.09  # Backward-subsumed                    : 1063
% 3.89/4.09  # Backward-rewritten                   : 75
% 3.89/4.09  # Generated clauses                    : 58253
% 3.89/4.09  # ...of the previous two non-trivial   : 58075
% 3.89/4.09  # Contextual simplify-reflections      : 1704
% 3.89/4.09  # Paramodulations                      : 58160
% 3.89/4.09  # Factorizations                       : 2
% 3.89/4.09  # Equation resolutions                 : 91
% 3.89/4.09  # Propositional unsat checks           : 0
% 3.89/4.09  #    Propositional check models        : 0
% 3.89/4.09  #    Propositional check unsatisfiable : 0
% 3.89/4.09  #    Propositional clauses             : 0
% 3.89/4.09  #    Propositional clauses after purity: 0
% 3.89/4.09  #    Propositional unsat core size     : 0
% 3.89/4.09  #    Propositional preprocessing time  : 0.000
% 3.89/4.09  #    Propositional encoding time       : 0.000
% 3.89/4.09  #    Propositional solver time         : 0.000
% 3.89/4.09  #    Success case prop preproc time    : 0.000
% 3.89/4.09  #    Success case prop encoding time   : 0.000
% 3.89/4.09  #    Success case prop solver time     : 0.000
% 3.89/4.09  # Current number of processed clauses  : 3031
% 3.89/4.09  #    Positive orientable unit clauses  : 59
% 3.89/4.09  #    Positive unorientable unit clauses: 0
% 3.89/4.09  #    Negative unit clauses             : 4
% 3.89/4.09  #    Non-unit-clauses                  : 2968
% 3.89/4.09  # Current number of unprocessed clauses: 46642
% 3.89/4.09  # ...number of literals in the above   : 756663
% 3.89/4.09  # Current number of archived formulas  : 0
% 3.89/4.09  # Current number of archived clauses   : 1173
% 3.89/4.09  # Clause-clause subsumption calls (NU) : 8257101
% 3.89/4.09  # Rec. Clause-clause subsumption calls : 342766
% 3.89/4.09  # Non-unit clause-clause subsumptions  : 9560
% 3.89/4.09  # Unit Clause-clause subsumption calls : 21834
% 3.89/4.09  # Rewrite failures with RHS unbound    : 0
% 3.89/4.09  # BW rewrite match attempts            : 2233
% 3.89/4.09  # BW rewrite match successes           : 11
% 3.89/4.09  # Condensation attempts                : 0
% 3.89/4.09  # Condensation successes               : 0
% 3.89/4.09  # Termbank termtop insertions          : 4898062
% 3.89/4.10  
% 3.89/4.10  # -------------------------------------------------
% 3.89/4.10  # User time                : 3.668 s
% 3.89/4.10  # System time              : 0.068 s
% 3.89/4.10  # Total time               : 3.737 s
% 3.89/4.10  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
