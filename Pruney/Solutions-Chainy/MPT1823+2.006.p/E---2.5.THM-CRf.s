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
% DateTime   : Thu Dec  3 11:18:35 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   98 (1399 expanded)
%              Number of clauses        :   73 ( 434 expanded)
%              Number of leaves         :   12 ( 339 expanded)
%              Depth                    :   16
%              Number of atoms          :  674 (15346 expanded)
%              Number of equality atoms :   25 ( 895 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal clause size      :   51 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t139_tmap_1,conjecture,(
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
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( X1 = k1_tsep_1(X1,X3,X4)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                       => r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2),X5,k10_tmap_1(X1,X2,X3,X4,k2_tmap_1(X1,X2,X5,X3),k2_tmap_1(X1,X2,X5,X4))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_tmap_1)).

fof(dt_k3_tmap_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & m1_pre_topc(X3,X1)
        & m1_pre_topc(X4,X1)
        & v1_funct_1(X5)
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
     => ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
        & v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(dt_k10_tmap_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1)
        & ~ v2_struct_0(X4)
        & m1_pre_topc(X4,X1)
        & v1_funct_1(X5)
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
        & v1_funct_1(X6)
        & v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
     => ( v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))
        & v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
        & m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).

fof(d5_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X4,X3)
                       => k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(t7_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X2)
             => m1_pre_topc(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

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

fof(t138_tmap_1,axiom,(
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
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
                     => r2_funct_2(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2),X5,k10_tmap_1(X1,X2,X3,X4,k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_tmap_1)).

fof(redefinition_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_funct_2(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(reflexivity_r1_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X4)
        & v1_funct_1(X5)
        & v1_funct_2(X5,X1,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & v1_funct_2(X6,X3,X4)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => r1_funct_2(X1,X2,X3,X4,X5,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

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

fof(c_0_12,negated_conjecture,(
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
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ( X1 = k1_tsep_1(X1,X3,X4)
                     => ! [X5] :
                          ( ( v1_funct_1(X5)
                            & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                         => r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2),X5,k10_tmap_1(X1,X2,X3,X4,k2_tmap_1(X1,X2,X5,X3),k2_tmap_1(X1,X2,X5,X4))) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t139_tmap_1])).

fof(c_0_13,plain,(
    ! [X34,X35,X36,X37,X38] :
      ( ( v1_funct_1(k3_tmap_1(X34,X35,X36,X37,X38))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ m1_pre_topc(X36,X34)
        | ~ m1_pre_topc(X37,X34)
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X35))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35)))) )
      & ( v1_funct_2(k3_tmap_1(X34,X35,X36,X37,X38),u1_struct_0(X37),u1_struct_0(X35))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ m1_pre_topc(X36,X34)
        | ~ m1_pre_topc(X37,X34)
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X35))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35)))) )
      & ( m1_subset_1(k3_tmap_1(X34,X35,X36,X37,X38),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X35))))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | ~ m1_pre_topc(X36,X34)
        | ~ m1_pre_topc(X37,X34)
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X35))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & esk1_0 = k1_tsep_1(esk1_0,esk3_0,esk4_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & ~ r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),esk5_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X44] :
      ( ~ l1_pre_topc(X44)
      | m1_pre_topc(X44,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_16,plain,
    ( m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,plain,
    ( v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_27,plain,(
    ! [X28,X29,X30,X31,X32,X33] :
      ( ( v1_funct_1(k10_tmap_1(X28,X29,X30,X31,X32,X33))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X28)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X29))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X29))))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X29))
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X29)))) )
      & ( v1_funct_2(k10_tmap_1(X28,X29,X30,X31,X32,X33),u1_struct_0(k1_tsep_1(X28,X30,X31)),u1_struct_0(X29))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X28)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X29))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X29))))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X29))
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X29)))) )
      & ( m1_subset_1(k10_tmap_1(X28,X29,X30,X31,X32,X33),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X30,X31)),u1_struct_0(X29))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X28)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X28)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X29))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X29))))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X29))
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X29)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_tmap_1])])])])).

cnf(c_0_28,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0))
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0),u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_34,plain,
    ( m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_24])]),c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_29]),c_0_30]),c_0_24])]),c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_29]),c_0_30]),c_0_24])]),c_0_31])).

cnf(c_0_38,plain,
    ( v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_40,plain,(
    ! [X23,X24,X25,X26,X27] :
      ( v2_struct_0(X23)
      | ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | ~ m1_pre_topc(X25,X23)
      | ~ m1_pre_topc(X26,X23)
      | ~ v1_funct_1(X27)
      | ~ v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(X24))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X24))))
      | ~ m1_pre_topc(X26,X25)
      | k3_tmap_1(X23,X24,X25,X26,X27) = k2_partfun1(u1_struct_0(X25),u1_struct_0(X24),X27,u1_struct_0(X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_41,plain,(
    ! [X45,X46,X47] :
      ( ~ v2_pre_topc(X45)
      | ~ l1_pre_topc(X45)
      | ~ m1_pre_topc(X46,X45)
      | ~ m1_pre_topc(X47,X46)
      | m1_pre_topc(X47,X45) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_42,plain,(
    ! [X19,X20,X21,X22] :
      ( v2_struct_0(X19)
      | ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | v2_struct_0(X20)
      | ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | ~ v1_funct_1(X21)
      | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
      | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
      | ~ m1_pre_topc(X22,X19)
      | k2_tmap_1(X19,X20,X21,X22) = k2_partfun1(u1_struct_0(X19),u1_struct_0(X20),X21,u1_struct_0(X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_43,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | m1_subset_1(k10_tmap_1(X1,esk2_0,X2,X3,X4,k3_tmap_1(esk1_0,esk2_0,esk1_0,X3,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(X3,esk1_0)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_18]),c_0_19])]),c_0_22]),c_0_36]),c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v1_funct_1(k10_tmap_1(X1,esk2_0,X2,X3,X4,k3_tmap_1(esk1_0,esk2_0,esk1_0,X3,esk5_0)))
    | ~ m1_pre_topc(X3,esk1_0)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_35]),c_0_18]),c_0_19])]),c_0_22]),c_0_36]),c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v1_funct_2(k10_tmap_1(X1,esk2_0,X2,X3,X4,k3_tmap_1(esk1_0,esk2_0,esk1_0,X3,esk5_0)),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X3,esk1_0)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_35]),c_0_18]),c_0_19])]),c_0_22]),c_0_36]),c_0_37])).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | m1_subset_1(k10_tmap_1(X3,esk2_0,X2,X1,k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_50,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_51,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_52,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v1_funct_1(k10_tmap_1(X3,esk2_0,X2,X1,k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0)))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_53,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v1_funct_2(k10_tmap_1(X3,esk2_0,X2,X1,k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_54,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5) ),
    inference(csr,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X1)) = k2_tmap_1(esk1_0,esk2_0,esk5_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_17]),c_0_18]),c_0_30]),c_0_19]),c_0_24]),c_0_20]),c_0_21])]),c_0_22]),c_0_31])).

cnf(c_0_56,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_57,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_59,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v1_funct_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)))
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_50]),c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v1_funct_2(k10_tmap_1(X1,esk2_0,X2,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_50]),c_0_51])).

fof(c_0_61,plain,(
    ! [X39,X40,X41,X42,X43] :
      ( v2_struct_0(X39)
      | ~ v2_pre_topc(X39)
      | ~ l1_pre_topc(X39)
      | v2_struct_0(X40)
      | ~ v2_pre_topc(X40)
      | ~ l1_pre_topc(X40)
      | v2_struct_0(X41)
      | ~ m1_pre_topc(X41,X39)
      | v2_struct_0(X42)
      | ~ m1_pre_topc(X42,X39)
      | ~ v1_funct_1(X43)
      | ~ v1_funct_2(X43,u1_struct_0(k1_tsep_1(X39,X41,X42)),u1_struct_0(X40))
      | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X39,X41,X42)),u1_struct_0(X40))))
      | r2_funct_2(u1_struct_0(k1_tsep_1(X39,X41,X42)),u1_struct_0(X40),X43,k10_tmap_1(X39,X40,X41,X42,k3_tmap_1(X39,X40,k1_tsep_1(X39,X41,X42),X41,X43),k3_tmap_1(X39,X40,k1_tsep_1(X39,X41,X42),X42,X43))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t138_tmap_1])])])])).

cnf(c_0_62,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_63,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0)) = k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_50])).

cnf(c_0_64,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0)) = k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

fof(c_0_65,plain,(
    ! [X7,X8,X9,X10] :
      ( ( ~ r2_funct_2(X7,X8,X9,X10)
        | X9 = X10
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X7,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( X9 != X10
        | r2_funct_2(X7,X8,X9,X10)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X7,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_66,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_56]),c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( esk1_0 = k1_tsep_1(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_68,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_56]),c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_56]),c_0_58])).

cnf(c_0_70,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | r2_funct_2(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2),X5,k10_tmap_1(X1,X2,X3,X4,k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_71,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( v1_xboole_0(X14)
      | v1_xboole_0(X16)
      | ~ v1_funct_1(X17)
      | ~ v1_funct_2(X17,X13,X14)
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | ~ v1_funct_1(X18)
      | ~ v1_funct_2(X18,X15,X16)
      | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | r1_funct_2(X13,X14,X15,X16,X17,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r1_funct_2])])])).

cnf(c_0_72,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),esk5_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_73,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,esk4_0,esk5_0) = k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_50]),c_0_63])).

cnf(c_0_74,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,esk3_0,esk5_0) = k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_56]),c_0_64])).

cnf(c_0_75,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_50]),c_0_67]),c_0_56]),c_0_30]),c_0_24])]),c_0_31])).

cnf(c_0_77,negated_conjecture,
    ( v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_50]),c_0_56]),c_0_30]),c_0_24])]),c_0_31])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_50]),c_0_67]),c_0_56]),c_0_30]),c_0_24])]),c_0_31])).

cnf(c_0_79,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(X1),X2,k10_tmap_1(esk1_0,X1,esk3_0,esk4_0,k3_tmap_1(esk1_0,X1,esk1_0,esk3_0,X2),k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_67]),c_0_50]),c_0_56]),c_0_30]),c_0_24])]),c_0_51]),c_0_58]),c_0_31])).

cnf(c_0_80,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r1_funct_2(X4,X1,X6,X2,X3,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X6,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_72,c_0_67])).

cnf(c_0_82,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0) = k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_29]),c_0_30]),c_0_24])]),c_0_31])).

cnf(c_0_83,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0) = k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_29]),c_0_30]),c_0_24])]),c_0_31])).

cnf(c_0_84,negated_conjecture,
    ( X1 = k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0))
    | ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X1,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])]),c_0_78])])).

cnf(c_0_85,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_86,negated_conjecture,
    ( r1_funct_2(X1,X2,u1_struct_0(esk1_0),u1_struct_0(esk2_0),X3,X3)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_17]),c_0_20]),c_0_21])])).

cnf(c_0_87,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82]),c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_17]),c_0_20]),c_0_21])])).

fof(c_0_89,plain,(
    ! [X12] :
      ( v2_struct_0(X12)
      | ~ l1_struct_0(X12)
      | ~ v1_xboole_0(u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_90,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk5_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_17]),c_0_20]),c_0_21])])).

cnf(c_0_91,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_92,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[c_0_90,c_0_91])).

fof(c_0_94,plain,(
    ! [X11] :
      ( ~ l1_pre_topc(X11)
      | l1_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_95,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_22])).

cnf(c_0_96,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:13:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 2.01/2.18  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S059I
% 2.01/2.18  # and selection function SelectComplexExceptUniqMaxPosHorn.
% 2.01/2.18  #
% 2.01/2.18  # Preprocessing time       : 0.030 s
% 2.01/2.18  # Presaturation interreduction done
% 2.01/2.18  
% 2.01/2.18  # Proof found!
% 2.01/2.18  # SZS status Theorem
% 2.01/2.18  # SZS output start CNFRefutation
% 2.01/2.18  fof(t139_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(X1=k1_tsep_1(X1,X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2),X5,k10_tmap_1(X1,X2,X3,X4,k2_tmap_1(X1,X2,X5,X3),k2_tmap_1(X1,X2,X5,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_tmap_1)).
% 2.01/2.18  fof(dt_k3_tmap_1, axiom, ![X1, X2, X3, X4, X5]:(((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&m1_pre_topc(X3,X1))&m1_pre_topc(X4,X1))&v1_funct_1(X5))&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>((v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))&v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 2.01/2.18  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 2.01/2.18  fof(dt_k10_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))&~(v2_struct_0(X4)))&m1_pre_topc(X4,X1))&v1_funct_1(X5))&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(X6))&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 2.01/2.18  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.01/2.19  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 2.01/2.19  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.01/2.19  fof(t138_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))=>r2_funct_2(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2),X5,k10_tmap_1(X1,X2,X3,X4,k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_tmap_1)).
% 2.01/2.19  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 2.01/2.19  fof(reflexivity_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>r1_funct_2(X1,X2,X3,X4,X5,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r1_funct_2)).
% 2.01/2.19  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.01/2.19  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.01/2.19  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(X1=k1_tsep_1(X1,X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2),X5,k10_tmap_1(X1,X2,X3,X4,k2_tmap_1(X1,X2,X5,X3),k2_tmap_1(X1,X2,X5,X4)))))))))), inference(assume_negation,[status(cth)],[t139_tmap_1])).
% 2.01/2.19  fof(c_0_13, plain, ![X34, X35, X36, X37, X38]:(((v1_funct_1(k3_tmap_1(X34,X35,X36,X37,X38))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_pre_topc(X36,X34)|~m1_pre_topc(X37,X34)|~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X35))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35))))))&(v1_funct_2(k3_tmap_1(X34,X35,X36,X37,X38),u1_struct_0(X37),u1_struct_0(X35))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_pre_topc(X36,X34)|~m1_pre_topc(X37,X34)|~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X35))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35)))))))&(m1_subset_1(k3_tmap_1(X34,X35,X36,X37,X38),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X35))))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|~m1_pre_topc(X36,X34)|~m1_pre_topc(X37,X34)|~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X35))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).
% 2.01/2.19  fof(c_0_14, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(esk1_0=k1_tsep_1(esk1_0,esk3_0,esk4_0)&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&~r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),esk5_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 2.01/2.19  fof(c_0_15, plain, ![X44]:(~l1_pre_topc(X44)|m1_pre_topc(X44,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 2.01/2.19  cnf(c_0_16, plain, (m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.01/2.19  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.01/2.19  cnf(c_0_18, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.01/2.19  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.01/2.19  cnf(c_0_20, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.01/2.19  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.01/2.19  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.01/2.19  cnf(c_0_23, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.01/2.19  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.01/2.19  cnf(c_0_25, plain, (v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.01/2.19  cnf(c_0_26, plain, (v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.01/2.19  fof(c_0_27, plain, ![X28, X29, X30, X31, X32, X33]:(((v1_funct_1(k10_tmap_1(X28,X29,X30,X31,X32,X33))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|v2_struct_0(X30)|~m1_pre_topc(X30,X28)|v2_struct_0(X31)|~m1_pre_topc(X31,X28)|~v1_funct_1(X32)|~v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X29))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X29))))|~v1_funct_1(X33)|~v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X29))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X29))))))&(v1_funct_2(k10_tmap_1(X28,X29,X30,X31,X32,X33),u1_struct_0(k1_tsep_1(X28,X30,X31)),u1_struct_0(X29))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|v2_struct_0(X30)|~m1_pre_topc(X30,X28)|v2_struct_0(X31)|~m1_pre_topc(X31,X28)|~v1_funct_1(X32)|~v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X29))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X29))))|~v1_funct_1(X33)|~v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X29))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X29)))))))&(m1_subset_1(k10_tmap_1(X28,X29,X30,X31,X32,X33),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X30,X31)),u1_struct_0(X29))))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|v2_struct_0(X30)|~m1_pre_topc(X30,X28)|v2_struct_0(X31)|~m1_pre_topc(X31,X28)|~v1_funct_1(X32)|~v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X29))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X29))))|~v1_funct_1(X33)|~v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X29))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X29))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_tmap_1])])])])).
% 2.01/2.19  cnf(c_0_28, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 2.01/2.19  cnf(c_0_29, negated_conjecture, (m1_pre_topc(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 2.01/2.19  cnf(c_0_30, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.01/2.19  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.01/2.19  cnf(c_0_32, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0))|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 2.01/2.19  cnf(c_0_33, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0),u1_struct_0(X2),u1_struct_0(esk2_0))|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 2.01/2.19  cnf(c_0_34, plain, (m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.01/2.19  cnf(c_0_35, negated_conjecture, (m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_24])]), c_0_31])).
% 2.01/2.19  cnf(c_0_36, negated_conjecture, (v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_29]), c_0_30]), c_0_24])]), c_0_31])).
% 2.01/2.19  cnf(c_0_37, negated_conjecture, (v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0),u1_struct_0(X1),u1_struct_0(esk2_0))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_29]), c_0_30]), c_0_24])]), c_0_31])).
% 2.01/2.19  cnf(c_0_38, plain, (v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.01/2.19  cnf(c_0_39, plain, (v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.01/2.19  fof(c_0_40, plain, ![X23, X24, X25, X26, X27]:(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|(~m1_pre_topc(X25,X23)|(~m1_pre_topc(X26,X23)|(~v1_funct_1(X27)|~v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(X24))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X24))))|(~m1_pre_topc(X26,X25)|k3_tmap_1(X23,X24,X25,X26,X27)=k2_partfun1(u1_struct_0(X25),u1_struct_0(X24),X27,u1_struct_0(X26)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 2.01/2.19  fof(c_0_41, plain, ![X45, X46, X47]:(~v2_pre_topc(X45)|~l1_pre_topc(X45)|(~m1_pre_topc(X46,X45)|(~m1_pre_topc(X47,X46)|m1_pre_topc(X47,X45)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 2.01/2.19  fof(c_0_42, plain, ![X19, X20, X21, X22]:(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))|(~m1_pre_topc(X22,X19)|k2_tmap_1(X19,X20,X21,X22)=k2_partfun1(u1_struct_0(X19),u1_struct_0(X20),X21,u1_struct_0(X22)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 2.01/2.19  cnf(c_0_43, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|m1_subset_1(k10_tmap_1(X1,esk2_0,X2,X3,X4,k3_tmap_1(esk1_0,esk2_0,esk1_0,X3,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk2_0))))|~m1_pre_topc(X3,esk1_0)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X4)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_18]), c_0_19])]), c_0_22]), c_0_36]), c_0_37])).
% 2.01/2.19  cnf(c_0_44, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v1_funct_1(k10_tmap_1(X1,esk2_0,X2,X3,X4,k3_tmap_1(esk1_0,esk2_0,esk1_0,X3,esk5_0)))|~m1_pre_topc(X3,esk1_0)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X4)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_35]), c_0_18]), c_0_19])]), c_0_22]), c_0_36]), c_0_37])).
% 2.01/2.19  cnf(c_0_45, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v1_funct_2(k10_tmap_1(X1,esk2_0,X2,X3,X4,k3_tmap_1(esk1_0,esk2_0,esk1_0,X3,esk5_0)),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk2_0))|~m1_pre_topc(X3,esk1_0)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X4)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_35]), c_0_18]), c_0_19])]), c_0_22]), c_0_36]), c_0_37])).
% 2.01/2.19  cnf(c_0_46, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.01/2.19  cnf(c_0_47, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 2.01/2.19  cnf(c_0_48, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 2.01/2.19  cnf(c_0_49, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|m1_subset_1(k10_tmap_1(X3,esk2_0,X2,X1,k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(esk2_0))))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,X3)|~m1_pre_topc(X2,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_35]), c_0_36]), c_0_37])).
% 2.01/2.19  cnf(c_0_50, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.01/2.19  cnf(c_0_51, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.01/2.19  cnf(c_0_52, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v1_funct_1(k10_tmap_1(X3,esk2_0,X2,X1,k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0)))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,X3)|~m1_pre_topc(X2,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_35]), c_0_36]), c_0_37])).
% 2.01/2.19  cnf(c_0_53, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v1_funct_2(k10_tmap_1(X3,esk2_0,X2,X1,k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0)),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(esk2_0))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,X3)|~m1_pre_topc(X2,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_35]), c_0_36]), c_0_37])).
% 2.01/2.19  cnf(c_0_54, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)), inference(csr,[status(thm)],[c_0_46, c_0_47])).
% 2.01/2.19  cnf(c_0_55, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X1))=k2_tmap_1(esk1_0,esk2_0,esk5_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_17]), c_0_18]), c_0_30]), c_0_19]), c_0_24]), c_0_20]), c_0_21])]), c_0_22]), c_0_31])).
% 2.01/2.19  cnf(c_0_56, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.01/2.19  cnf(c_0_57, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))))|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 2.01/2.19  cnf(c_0_58, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.01/2.19  cnf(c_0_59, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|v1_funct_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)))|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_50]), c_0_51])).
% 2.01/2.19  cnf(c_0_60, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|v1_funct_2(k10_tmap_1(X1,esk2_0,X2,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_50]), c_0_51])).
% 2.01/2.19  fof(c_0_61, plain, ![X39, X40, X41, X42, X43]:(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|(v2_struct_0(X41)|~m1_pre_topc(X41,X39)|(v2_struct_0(X42)|~m1_pre_topc(X42,X39)|(~v1_funct_1(X43)|~v1_funct_2(X43,u1_struct_0(k1_tsep_1(X39,X41,X42)),u1_struct_0(X40))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X39,X41,X42)),u1_struct_0(X40))))|r2_funct_2(u1_struct_0(k1_tsep_1(X39,X41,X42)),u1_struct_0(X40),X43,k10_tmap_1(X39,X40,X41,X42,k3_tmap_1(X39,X40,k1_tsep_1(X39,X41,X42),X41,X43),k3_tmap_1(X39,X40,k1_tsep_1(X39,X41,X42),X42,X43)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t138_tmap_1])])])])).
% 2.01/2.19  cnf(c_0_62, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0)=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(esk1_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 2.01/2.19  cnf(c_0_63, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0))=k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_55, c_0_50])).
% 2.01/2.19  cnf(c_0_64, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0))=k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 2.01/2.19  fof(c_0_65, plain, ![X7, X8, X9, X10]:((~r2_funct_2(X7,X8,X9,X10)|X9=X10|(~v1_funct_1(X9)|~v1_funct_2(X9,X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|~v1_funct_1(X10)|~v1_funct_2(X10,X7,X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))&(X9!=X10|r2_funct_2(X7,X8,X9,X10)|(~v1_funct_1(X9)|~v1_funct_2(X9,X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|~v1_funct_1(X10)|~v1_funct_2(X10,X7,X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 2.01/2.19  cnf(c_0_66, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_56]), c_0_58])).
% 2.01/2.19  cnf(c_0_67, negated_conjecture, (esk1_0=k1_tsep_1(esk1_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.01/2.19  cnf(c_0_68, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_56]), c_0_58])).
% 2.01/2.19  cnf(c_0_69, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_56]), c_0_58])).
% 2.01/2.19  cnf(c_0_70, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|r2_funct_2(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2),X5,k10_tmap_1(X1,X2,X3,X4,k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 2.01/2.19  fof(c_0_71, plain, ![X13, X14, X15, X16, X17, X18]:(v1_xboole_0(X14)|v1_xboole_0(X16)|~v1_funct_1(X17)|~v1_funct_2(X17,X13,X14)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|~v1_funct_1(X18)|~v1_funct_2(X18,X15,X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|r1_funct_2(X13,X14,X15,X16,X17,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r1_funct_2])])])).
% 2.01/2.19  cnf(c_0_72, negated_conjecture, (~r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),esk5_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.01/2.19  cnf(c_0_73, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,esk4_0,esk5_0)=k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)|v2_struct_0(X1)|~m1_pre_topc(esk1_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_50]), c_0_63])).
% 2.01/2.19  cnf(c_0_74, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,esk3_0,esk5_0)=k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)|v2_struct_0(X1)|~m1_pre_topc(esk1_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_56]), c_0_64])).
% 2.01/2.19  cnf(c_0_75, plain, (X3=X4|~r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 2.01/2.19  cnf(c_0_76, negated_conjecture, (m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_50]), c_0_67]), c_0_56]), c_0_30]), c_0_24])]), c_0_31])).
% 2.01/2.19  cnf(c_0_77, negated_conjecture, (v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_50]), c_0_56]), c_0_30]), c_0_24])]), c_0_31])).
% 2.01/2.19  cnf(c_0_78, negated_conjecture, (v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)),u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_50]), c_0_67]), c_0_56]), c_0_30]), c_0_24])]), c_0_31])).
% 2.01/2.19  cnf(c_0_79, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(X1),X2,k10_tmap_1(esk1_0,X1,esk3_0,esk4_0,k3_tmap_1(esk1_0,X1,esk1_0,esk3_0,X2),k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_67]), c_0_50]), c_0_56]), c_0_30]), c_0_24])]), c_0_51]), c_0_58]), c_0_31])).
% 2.01/2.19  cnf(c_0_80, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r1_funct_2(X4,X1,X6,X2,X3,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,X4,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))|~v1_funct_1(X5)|~v1_funct_2(X5,X6,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X2)))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 2.01/2.19  cnf(c_0_81, negated_conjecture, (~r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)))), inference(rw,[status(thm)],[c_0_72, c_0_67])).
% 2.01/2.19  cnf(c_0_82, negated_conjecture, (k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)=k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_29]), c_0_30]), c_0_24])]), c_0_31])).
% 2.01/2.19  cnf(c_0_83, negated_conjecture, (k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)=k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_29]), c_0_30]), c_0_24])]), c_0_31])).
% 2.01/2.19  cnf(c_0_84, negated_conjecture, (X1=k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0))|~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),X1,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))|~v1_funct_2(X1,u1_struct_0(esk1_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])]), c_0_78])])).
% 2.01/2.19  cnf(c_0_85, negated_conjecture, (r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 2.01/2.19  cnf(c_0_86, negated_conjecture, (r1_funct_2(X1,X2,u1_struct_0(esk1_0),u1_struct_0(esk2_0),X3,X3)|v1_xboole_0(u1_struct_0(esk2_0))|v1_xboole_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_17]), c_0_20]), c_0_21])])).
% 2.01/2.19  cnf(c_0_87, negated_conjecture, (~r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82]), c_0_83])).
% 2.01/2.19  cnf(c_0_88, negated_conjecture, (k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_17]), c_0_20]), c_0_21])])).
% 2.01/2.19  fof(c_0_89, plain, ![X12]:(v2_struct_0(X12)|~l1_struct_0(X12)|~v1_xboole_0(u1_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 2.01/2.19  cnf(c_0_90, negated_conjecture, (r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk5_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_17]), c_0_20]), c_0_21])])).
% 2.01/2.19  cnf(c_0_91, negated_conjecture, (~r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk5_0)), inference(rw,[status(thm)],[c_0_87, c_0_88])).
% 2.01/2.19  cnf(c_0_92, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_89])).
% 2.01/2.19  cnf(c_0_93, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[c_0_90, c_0_91])).
% 2.01/2.19  fof(c_0_94, plain, ![X11]:(~l1_pre_topc(X11)|l1_struct_0(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 2.01/2.19  cnf(c_0_95, negated_conjecture, (~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_22])).
% 2.01/2.19  cnf(c_0_96, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 2.01/2.19  cnf(c_0_97, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_19])]), ['proof']).
% 2.01/2.19  # SZS output end CNFRefutation
% 2.01/2.19  # Proof object total steps             : 98
% 2.01/2.19  # Proof object clause steps            : 73
% 2.01/2.19  # Proof object formula steps           : 25
% 2.01/2.19  # Proof object conjectures             : 60
% 2.01/2.19  # Proof object clause conjectures      : 57
% 2.01/2.19  # Proof object formula conjectures     : 3
% 2.01/2.19  # Proof object initial clauses used    : 30
% 2.01/2.19  # Proof object initial formulas used   : 12
% 2.01/2.19  # Proof object generating inferences   : 38
% 2.01/2.19  # Proof object simplifying inferences  : 139
% 2.01/2.19  # Training examples: 0 positive, 0 negative
% 2.01/2.19  # Parsed axioms                        : 12
% 2.01/2.19  # Removed by relevancy pruning/SinE    : 0
% 2.01/2.19  # Initial clauses                      : 31
% 2.01/2.19  # Removed in clause preprocessing      : 0
% 2.01/2.19  # Initial clauses in saturation        : 31
% 2.01/2.19  # Processed clauses                    : 4525
% 2.01/2.19  # ...of these trivial                  : 1
% 2.01/2.19  # ...subsumed                          : 231
% 2.01/2.19  # ...remaining for further processing  : 4293
% 2.01/2.19  # Other redundant clauses eliminated   : 1
% 2.01/2.19  # Clauses deleted for lack of memory   : 0
% 2.01/2.19  # Backward-subsumed                    : 35
% 2.01/2.19  # Backward-rewritten                   : 781
% 2.01/2.19  # Generated clauses                    : 24391
% 2.01/2.19  # ...of the previous two non-trivial   : 24542
% 2.01/2.19  # Contextual simplify-reflections      : 713
% 2.01/2.19  # Paramodulations                      : 24389
% 2.01/2.19  # Factorizations                       : 0
% 2.01/2.19  # Equation resolutions                 : 1
% 2.01/2.19  # Propositional unsat checks           : 0
% 2.01/2.19  #    Propositional check models        : 0
% 2.01/2.19  #    Propositional check unsatisfiable : 0
% 2.01/2.19  #    Propositional clauses             : 0
% 2.01/2.19  #    Propositional clauses after purity: 0
% 2.01/2.19  #    Propositional unsat core size     : 0
% 2.01/2.19  #    Propositional preprocessing time  : 0.000
% 2.01/2.19  #    Propositional encoding time       : 0.000
% 2.01/2.19  #    Propositional solver time         : 0.000
% 2.01/2.19  #    Success case prop preproc time    : 0.000
% 2.01/2.19  #    Success case prop encoding time   : 0.000
% 2.01/2.19  #    Success case prop solver time     : 0.000
% 2.01/2.19  # Current number of processed clauses  : 3444
% 2.01/2.19  #    Positive orientable unit clauses  : 852
% 2.01/2.19  #    Positive unorientable unit clauses: 0
% 2.01/2.19  #    Negative unit clauses             : 6
% 2.01/2.19  #    Non-unit-clauses                  : 2586
% 2.01/2.19  # Current number of unprocessed clauses: 20079
% 2.01/2.19  # ...number of literals in the above   : 159071
% 2.01/2.19  # Current number of archived formulas  : 0
% 2.01/2.19  # Current number of archived clauses   : 848
% 2.01/2.19  # Clause-clause subsumption calls (NU) : 3120724
% 2.01/2.19  # Rec. Clause-clause subsumption calls : 142024
% 2.01/2.19  # Non-unit clause-clause subsumptions  : 979
% 2.01/2.19  # Unit Clause-clause subsumption calls : 340586
% 2.01/2.19  # Rewrite failures with RHS unbound    : 0
% 2.01/2.19  # BW rewrite match attempts            : 117731
% 2.01/2.19  # BW rewrite match successes           : 42
% 2.01/2.19  # Condensation attempts                : 0
% 2.01/2.19  # Condensation successes               : 0
% 2.01/2.19  # Termbank termtop insertions          : 3300245
% 2.01/2.19  
% 2.01/2.19  # -------------------------------------------------
% 2.01/2.19  # User time                : 1.827 s
% 2.01/2.19  # System time              : 0.023 s
% 2.01/2.19  # Total time               : 1.850 s
% 2.01/2.19  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
