%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:09 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  111 (6173 expanded)
%              Number of clauses        :   76 (1987 expanded)
%              Number of leaves         :   17 (1538 expanded)
%              Depth                    :   20
%              Number of atoms          :  628 (50590 expanded)
%              Number of equality atoms :   40 (3493 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   48 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t96_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,u1_struct_0(X2))
                     => X4 = k1_funct_1(X3,X4) ) )
               => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).

fof(dt_k4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_funct_1(k4_tmap_1(X1,X2))
        & v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
        & m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).

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

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(t74_tmap_1,axiom,(
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
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                 => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).

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

fof(t59_tmap_1,axiom,(
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

fof(t95_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,u1_struct_0(X2))
               => k1_funct_1(k4_tmap_1(X1,X2),X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).

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

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_hidden(X4,u1_struct_0(X2))
                       => X4 = k1_funct_1(X3,X4) ) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t96_tmap_1])).

fof(c_0_18,plain,(
    ! [X40,X41] :
      ( ( v1_funct_1(k4_tmap_1(X40,X41))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | ~ m1_pre_topc(X41,X40) )
      & ( v1_funct_2(k4_tmap_1(X40,X41),u1_struct_0(X41),u1_struct_0(X40))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | ~ m1_pre_topc(X41,X40) )
      & ( m1_subset_1(k4_tmap_1(X40,X41),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X40))))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | ~ m1_pre_topc(X41,X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).

fof(c_0_19,negated_conjecture,(
    ! [X62] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk3_0)
      & v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
      & ( ~ m1_subset_1(X62,u1_struct_0(esk3_0))
        | ~ r2_hidden(X62,u1_struct_0(esk4_0))
        | X62 = k1_funct_1(esk5_0,X62) )
      & ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])])).

fof(c_0_20,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_pre_topc(X23,X22)
      | l1_pre_topc(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_21,plain,(
    ! [X19,X20] :
      ( ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | ~ m1_pre_topc(X20,X19)
      | v2_pre_topc(X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_22,plain,(
    ! [X31,X32,X33,X34,X35] :
      ( v2_struct_0(X31)
      | ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | v2_struct_0(X32)
      | ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | ~ m1_pre_topc(X33,X31)
      | ~ m1_pre_topc(X34,X31)
      | ~ v1_funct_1(X35)
      | ~ v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X32))
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X32))))
      | ~ m1_pre_topc(X34,X33)
      | k3_tmap_1(X31,X32,X33,X34,X35) = k2_partfun1(u1_struct_0(X33),u1_struct_0(X32),X35,u1_struct_0(X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_23,plain,(
    ! [X53,X54,X55] :
      ( ~ v2_pre_topc(X53)
      | ~ l1_pre_topc(X53)
      | ~ m1_pre_topc(X54,X53)
      | ~ m1_pre_topc(X55,X54)
      | m1_pre_topc(X55,X53) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_24,plain,(
    ! [X27,X28,X29,X30] :
      ( v2_struct_0(X27)
      | ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | v2_struct_0(X28)
      | ~ v2_pre_topc(X28)
      | ~ l1_pre_topc(X28)
      | ~ v1_funct_1(X29)
      | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28))))
      | ~ m1_pre_topc(X30,X27)
      | k2_tmap_1(X27,X28,X29,X30) = k2_partfun1(u1_struct_0(X27),u1_struct_0(X28),X29,u1_struct_0(X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_25,plain,
    ( v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,plain,
    ( v1_funct_1(k4_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
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

cnf(c_0_37,negated_conjecture,
    ( v1_funct_2(k4_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_26]),c_0_27])])).

cnf(c_0_39,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k4_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_1(k4_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_43,plain,(
    ! [X42] :
      ( ~ l1_pre_topc(X42)
      | m1_pre_topc(X42,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_44,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5) ),
    inference(csr,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),u1_struct_0(X1)) = k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_27]),c_0_38]),c_0_28]),c_0_39]),c_0_40]),c_0_41])]),c_0_29]),c_0_42])).

cnf(c_0_46,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_47,plain,(
    ! [X49,X50,X51,X52] :
      ( v2_struct_0(X49)
      | ~ v2_pre_topc(X49)
      | ~ l1_pre_topc(X49)
      | v2_struct_0(X50)
      | ~ v2_pre_topc(X50)
      | ~ l1_pre_topc(X50)
      | v2_struct_0(X51)
      | ~ m1_pre_topc(X51,X49)
      | ~ v1_funct_1(X52)
      | ~ v1_funct_2(X52,u1_struct_0(X51),u1_struct_0(X50))
      | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X50))))
      | r2_funct_2(u1_struct_0(X51),u1_struct_0(X50),X52,k3_tmap_1(X49,X50,X51,X51,X52)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_tmap_1])])])])).

cnf(c_0_48,negated_conjecture,
    ( k3_tmap_1(X1,esk3_0,esk4_0,X2,k4_tmap_1(esk3_0,esk4_0)) = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_37]),c_0_27]),c_0_28]),c_0_40]),c_0_41])]),c_0_29])).

cnf(c_0_49,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0)) = k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_38])])).

fof(c_0_50,plain,(
    ! [X36,X37,X38,X39] :
      ( ( v1_funct_1(k2_tmap_1(X36,X37,X38,X39))
        | ~ l1_struct_0(X36)
        | ~ l1_struct_0(X37)
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))
        | ~ l1_struct_0(X39) )
      & ( v1_funct_2(k2_tmap_1(X36,X37,X38,X39),u1_struct_0(X39),u1_struct_0(X37))
        | ~ l1_struct_0(X36)
        | ~ l1_struct_0(X37)
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))
        | ~ l1_struct_0(X39) )
      & ( m1_subset_1(k2_tmap_1(X36,X37,X38,X39),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X37))))
        | ~ l1_struct_0(X36)
        | ~ l1_struct_0(X37)
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))
        | ~ l1_struct_0(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( k3_tmap_1(X1,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0)) = k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_46]),c_0_49]),c_0_38])])).

cnf(c_0_53,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_54,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | l1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_55,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_57,plain,(
    ! [X15,X16,X17,X18] :
      ( ( ~ r2_funct_2(X15,X16,X17,X18)
        | X17 = X18
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( X17 != X18
        | r2_funct_2(X15,X16,X17,X18)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_58,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),k3_tmap_1(X1,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0)))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_37]),c_0_27]),c_0_28]),c_0_40]),c_0_41])]),c_0_42]),c_0_29])).

cnf(c_0_59,negated_conjecture,
    ( k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0)) = k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_46]),c_0_38]),c_0_39])]),c_0_42])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),X1),u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_37]),c_0_40]),c_0_41])])).

cnf(c_0_61,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),X1))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_37]),c_0_40]),c_0_41])])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_37]),c_0_40]),c_0_41])])).

cnf(c_0_64,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_46]),c_0_59]),c_0_38]),c_0_39])]),c_0_42])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),X1),u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_27])])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),X1))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_61]),c_0_27])])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_61]),c_0_27])])).

fof(c_0_69,plain,(
    ! [X43,X44,X45,X46,X47] :
      ( ( m1_subset_1(esk2_5(X43,X44,X45,X46,X47),u1_struct_0(X44))
        | r2_funct_2(u1_struct_0(X45),u1_struct_0(X43),k2_tmap_1(X44,X43,X46,X45),X47)
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,u1_struct_0(X45),u1_struct_0(X43))
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X43))))
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X43))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X43))))
        | v2_struct_0(X45)
        | ~ m1_pre_topc(X45,X44)
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( r2_hidden(esk2_5(X43,X44,X45,X46,X47),u1_struct_0(X45))
        | r2_funct_2(u1_struct_0(X45),u1_struct_0(X43),k2_tmap_1(X44,X43,X46,X45),X47)
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,u1_struct_0(X45),u1_struct_0(X43))
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X43))))
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X43))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X43))))
        | v2_struct_0(X45)
        | ~ m1_pre_topc(X45,X44)
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) )
      & ( k3_funct_2(u1_struct_0(X44),u1_struct_0(X43),X46,esk2_5(X43,X44,X45,X46,X47)) != k1_funct_1(X47,esk2_5(X43,X44,X45,X46,X47))
        | r2_funct_2(u1_struct_0(X45),u1_struct_0(X43),k2_tmap_1(X44,X43,X46,X45),X47)
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,u1_struct_0(X45),u1_struct_0(X43))
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X43))))
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X43))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X43))))
        | v2_struct_0(X45)
        | ~ m1_pre_topc(X45,X44)
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tmap_1])])])])])])).

cnf(c_0_70,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0) = k4_tmap_1(esk3_0,esk4_0)
    | ~ m1_subset_1(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
    | ~ v1_funct_2(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_40]),c_0_37]),c_0_41])])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),X1),u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_61]),c_0_38])])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),X1))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_61]),c_0_38])])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_61]),c_0_38])])).

cnf(c_0_74,plain,
    ( r2_hidden(esk2_5(X1,X2,X3,X4,X5),u1_struct_0(X3))
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_77,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_78,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0) = k4_tmap_1(esk3_0,esk4_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(X1,esk3_0,X2,esk4_0),esk5_0)
    | r2_hidden(esk2_5(esk3_0,X1,esk4_0,X2,esk5_0),u1_struct_0(esk4_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_27]),c_0_28]),c_0_76]),c_0_77])]),c_0_42]),c_0_29])).

cnf(c_0_80,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0) = k4_tmap_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_61]),c_0_38])])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_82,plain,
    ( m1_subset_1(esk2_5(X1,X2,X3,X4,X5),u1_struct_0(X2))
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_83,plain,(
    ! [X56,X57,X58] :
      ( v2_struct_0(X56)
      | ~ v2_pre_topc(X56)
      | ~ l1_pre_topc(X56)
      | v2_struct_0(X57)
      | ~ m1_pre_topc(X57,X56)
      | ~ m1_subset_1(X58,u1_struct_0(X56))
      | ~ r2_hidden(X58,u1_struct_0(X57))
      | k1_funct_1(k4_tmap_1(X56,X57),X58) = X58 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t95_tmap_1])])])])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))
    | ~ m1_pre_topc(esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_37]),c_0_80]),c_0_38]),c_0_39]),c_0_40]),c_0_41])]),c_0_42]),c_0_81])).

fof(c_0_85,plain,(
    ! [X24,X25,X26] :
      ( v2_struct_0(X24)
      | ~ l1_pre_topc(X24)
      | v2_struct_0(X25)
      | ~ m1_pre_topc(X25,X24)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | m1_subset_1(X26,u1_struct_0(X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_86,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(X1,esk3_0,X2,esk4_0),esk5_0)
    | m1_subset_1(esk2_5(esk3_0,X1,esk4_0,X2,esk5_0),u1_struct_0(X1))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_75]),c_0_27]),c_0_28]),c_0_76]),c_0_77])]),c_0_42]),c_0_29])).

fof(c_0_87,plain,(
    ! [X11,X12,X13,X14] :
      ( v1_xboole_0(X11)
      | ~ v1_funct_1(X13)
      | ~ v1_funct_2(X13,X11,X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ m1_subset_1(X14,X11)
      | k3_funct_2(X11,X12,X13,X14) = k1_funct_1(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_88,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_funct_1(k4_tmap_1(X1,X2),X3) = X3
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_46]),c_0_38])])).

cnf(c_0_90,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))
    | ~ m1_pre_topc(esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_37]),c_0_80]),c_0_38]),c_0_39]),c_0_40]),c_0_41])]),c_0_42]),c_0_81])).

cnf(c_0_92,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

fof(c_0_93,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_94,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(X1,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)) = esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_42])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_26]),c_0_27])]),c_0_42]),c_0_29])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_46]),c_0_38])])).

cnf(c_0_97,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),X1) = k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ m1_subset_1(k4_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_37]),c_0_41])])).

cnf(c_0_98,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)) = esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | ~ m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_101,negated_conjecture,
    ( X1 = k1_funct_1(esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_102,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),X1) = k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_40])])).

cnf(c_0_103,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_89])).

cnf(c_0_104,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)) = esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_100])])).

cnf(c_0_105,negated_conjecture,
    ( k1_funct_1(esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)) = esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | ~ m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_89])).

cnf(c_0_106,plain,
    ( r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k2_tmap_1(X1,X2,X3,X4),X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_5(X2,X1,X4,X3,X5)) != k1_funct_1(X5,esk2_5(X2,X1,X4,X3,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_107,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)) = esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_96]),c_0_103]),c_0_104])).

cnf(c_0_108,negated_conjecture,
    ( k1_funct_1(esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)) = esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_100])])).

cnf(c_0_109,negated_conjecture,
    ( ~ m1_pre_topc(esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_80]),c_0_108]),c_0_27]),c_0_38]),c_0_28]),c_0_39]),c_0_76]),c_0_40]),c_0_75]),c_0_37]),c_0_77]),c_0_41])]),c_0_42]),c_0_29]),c_0_81])).

cnf(c_0_110,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_46]),c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:22:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.19/0.39  # and selection function SelectCQIPrecWNTNp.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.030 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t96_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_tmap_1)).
% 0.19/0.39  fof(dt_k4_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k4_tmap_1(X1,X2))&v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 0.19/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.39  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.19/0.39  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.19/0.39  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.19/0.39  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.19/0.39  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.19/0.39  fof(t74_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tmap_1)).
% 0.19/0.39  fof(dt_k2_tmap_1, axiom, ![X1, X2, X3, X4]:((((((l1_struct_0(X1)&l1_struct_0(X2))&v1_funct_1(X3))&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))&l1_struct_0(X4))=>((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 0.19/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.39  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.19/0.39  fof(t59_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>(![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(r2_hidden(X6,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6)=k1_funct_1(X5,X6)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tmap_1)).
% 0.19/0.39  fof(t95_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,u1_struct_0(X2))=>k1_funct_1(k4_tmap_1(X1,X2),X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_tmap_1)).
% 0.19/0.39  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.19/0.39  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.19/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.39  fof(c_0_17, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3)))))), inference(assume_negation,[status(cth)],[t96_tmap_1])).
% 0.19/0.39  fof(c_0_18, plain, ![X40, X41]:(((v1_funct_1(k4_tmap_1(X40,X41))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|~m1_pre_topc(X41,X40)))&(v1_funct_2(k4_tmap_1(X40,X41),u1_struct_0(X41),u1_struct_0(X40))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|~m1_pre_topc(X41,X40))))&(m1_subset_1(k4_tmap_1(X40,X41),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X40))))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|~m1_pre_topc(X41,X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).
% 0.19/0.39  fof(c_0_19, negated_conjecture, ![X62]:(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))))&((~m1_subset_1(X62,u1_struct_0(esk3_0))|(~r2_hidden(X62,u1_struct_0(esk4_0))|X62=k1_funct_1(esk5_0,X62)))&~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])])).
% 0.19/0.39  fof(c_0_20, plain, ![X22, X23]:(~l1_pre_topc(X22)|(~m1_pre_topc(X23,X22)|l1_pre_topc(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.39  fof(c_0_21, plain, ![X19, X20]:(~v2_pre_topc(X19)|~l1_pre_topc(X19)|(~m1_pre_topc(X20,X19)|v2_pre_topc(X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.19/0.39  fof(c_0_22, plain, ![X31, X32, X33, X34, X35]:(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)|(~m1_pre_topc(X33,X31)|(~m1_pre_topc(X34,X31)|(~v1_funct_1(X35)|~v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X32))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X32))))|(~m1_pre_topc(X34,X33)|k3_tmap_1(X31,X32,X33,X34,X35)=k2_partfun1(u1_struct_0(X33),u1_struct_0(X32),X35,u1_struct_0(X34)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.19/0.39  fof(c_0_23, plain, ![X53, X54, X55]:(~v2_pre_topc(X53)|~l1_pre_topc(X53)|(~m1_pre_topc(X54,X53)|(~m1_pre_topc(X55,X54)|m1_pre_topc(X55,X53)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.19/0.39  fof(c_0_24, plain, ![X27, X28, X29, X30]:(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28))))|(~m1_pre_topc(X30,X27)|k2_tmap_1(X27,X28,X29,X30)=k2_partfun1(u1_struct_0(X27),u1_struct_0(X28),X29,u1_struct_0(X30)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.19/0.39  cnf(c_0_25, plain, (v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_26, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_28, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_30, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.39  cnf(c_0_31, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.39  cnf(c_0_32, plain, (m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_33, plain, (v1_funct_1(k4_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_34, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.39  cnf(c_0_35, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  cnf(c_0_36, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.39  cnf(c_0_37, negated_conjecture, (v1_funct_2(k4_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])]), c_0_29])).
% 0.19/0.39  cnf(c_0_38, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_26]), c_0_27])])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (v2_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_26]), c_0_27]), c_0_28])])).
% 0.19/0.39  cnf(c_0_40, negated_conjecture, (m1_subset_1(k4_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_26]), c_0_27]), c_0_28])]), c_0_29])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (v1_funct_1(k4_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_26]), c_0_27]), c_0_28])]), c_0_29])).
% 0.19/0.39  cnf(c_0_42, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  fof(c_0_43, plain, ![X42]:(~l1_pre_topc(X42)|m1_pre_topc(X42,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.19/0.39  cnf(c_0_44, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)), inference(csr,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.39  cnf(c_0_45, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),u1_struct_0(X1))=k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),X1)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_27]), c_0_38]), c_0_28]), c_0_39]), c_0_40]), c_0_41])]), c_0_29]), c_0_42])).
% 0.19/0.39  cnf(c_0_46, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.39  fof(c_0_47, plain, ![X49, X50, X51, X52]:(v2_struct_0(X49)|~v2_pre_topc(X49)|~l1_pre_topc(X49)|(v2_struct_0(X50)|~v2_pre_topc(X50)|~l1_pre_topc(X50)|(v2_struct_0(X51)|~m1_pre_topc(X51,X49)|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X51),u1_struct_0(X50))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X50))))|r2_funct_2(u1_struct_0(X51),u1_struct_0(X50),X52,k3_tmap_1(X49,X50,X51,X51,X52)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_tmap_1])])])])).
% 0.19/0.39  cnf(c_0_48, negated_conjecture, (k3_tmap_1(X1,esk3_0,esk4_0,X2,k4_tmap_1(esk3_0,esk4_0))=k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk4_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_37]), c_0_27]), c_0_28]), c_0_40]), c_0_41])]), c_0_29])).
% 0.19/0.39  cnf(c_0_49, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0))=k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_38])])).
% 0.19/0.39  fof(c_0_50, plain, ![X36, X37, X38, X39]:(((v1_funct_1(k2_tmap_1(X36,X37,X38,X39))|(~l1_struct_0(X36)|~l1_struct_0(X37)|~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))|~l1_struct_0(X39)))&(v1_funct_2(k2_tmap_1(X36,X37,X38,X39),u1_struct_0(X39),u1_struct_0(X37))|(~l1_struct_0(X36)|~l1_struct_0(X37)|~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))|~l1_struct_0(X39))))&(m1_subset_1(k2_tmap_1(X36,X37,X38,X39),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X37))))|(~l1_struct_0(X36)|~l1_struct_0(X37)|~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X36),u1_struct_0(X37))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X37))))|~l1_struct_0(X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).
% 0.19/0.39  cnf(c_0_51, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.39  cnf(c_0_52, negated_conjecture, (k3_tmap_1(X1,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0))=k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0)|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_46]), c_0_49]), c_0_38])])).
% 0.19/0.39  cnf(c_0_53, plain, (v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.39  fof(c_0_54, plain, ![X21]:(~l1_pre_topc(X21)|l1_struct_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.39  cnf(c_0_55, plain, (v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.39  cnf(c_0_56, plain, (m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.39  fof(c_0_57, plain, ![X15, X16, X17, X18]:((~r2_funct_2(X15,X16,X17,X18)|X17=X18|(~v1_funct_1(X17)|~v1_funct_2(X17,X15,X16)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|~v1_funct_1(X18)|~v1_funct_2(X18,X15,X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))))&(X17!=X18|r2_funct_2(X15,X16,X17,X18)|(~v1_funct_1(X17)|~v1_funct_2(X17,X15,X16)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|~v1_funct_1(X18)|~v1_funct_2(X18,X15,X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.19/0.39  cnf(c_0_58, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),k3_tmap_1(X1,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0)))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_37]), c_0_27]), c_0_28]), c_0_40]), c_0_41])]), c_0_42]), c_0_29])).
% 0.19/0.39  cnf(c_0_59, negated_conjecture, (k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0))=k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_46]), c_0_38]), c_0_39])]), c_0_42])).
% 0.19/0.39  cnf(c_0_60, negated_conjecture, (v1_funct_2(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),X1),u1_struct_0(X1),u1_struct_0(esk3_0))|~l1_struct_0(esk3_0)|~l1_struct_0(esk4_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_37]), c_0_40]), c_0_41])])).
% 0.19/0.39  cnf(c_0_61, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.39  cnf(c_0_62, negated_conjecture, (v1_funct_1(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),X1))|~l1_struct_0(esk3_0)|~l1_struct_0(esk4_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_37]), c_0_40]), c_0_41])])).
% 0.19/0.39  cnf(c_0_63, negated_conjecture, (m1_subset_1(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))|~l1_struct_0(esk3_0)|~l1_struct_0(esk4_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_37]), c_0_40]), c_0_41])])).
% 0.19/0.39  cnf(c_0_64, plain, (X3=X4|~r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.39  cnf(c_0_65, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_46]), c_0_59]), c_0_38]), c_0_39])]), c_0_42])).
% 0.19/0.39  cnf(c_0_66, negated_conjecture, (v1_funct_2(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),X1),u1_struct_0(X1),u1_struct_0(esk3_0))|~l1_struct_0(esk4_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_27])])).
% 0.19/0.39  cnf(c_0_67, negated_conjecture, (v1_funct_1(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),X1))|~l1_struct_0(esk4_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_61]), c_0_27])])).
% 0.19/0.39  cnf(c_0_68, negated_conjecture, (m1_subset_1(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))|~l1_struct_0(esk4_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_61]), c_0_27])])).
% 0.19/0.39  fof(c_0_69, plain, ![X43, X44, X45, X46, X47]:((m1_subset_1(esk2_5(X43,X44,X45,X46,X47),u1_struct_0(X44))|r2_funct_2(u1_struct_0(X45),u1_struct_0(X43),k2_tmap_1(X44,X43,X46,X45),X47)|(~v1_funct_1(X47)|~v1_funct_2(X47,u1_struct_0(X45),u1_struct_0(X43))|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X43)))))|(~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X43))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X43)))))|(v2_struct_0(X45)|~m1_pre_topc(X45,X44))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44))|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)))&((r2_hidden(esk2_5(X43,X44,X45,X46,X47),u1_struct_0(X45))|r2_funct_2(u1_struct_0(X45),u1_struct_0(X43),k2_tmap_1(X44,X43,X46,X45),X47)|(~v1_funct_1(X47)|~v1_funct_2(X47,u1_struct_0(X45),u1_struct_0(X43))|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X43)))))|(~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X43))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X43)))))|(v2_struct_0(X45)|~m1_pre_topc(X45,X44))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44))|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)))&(k3_funct_2(u1_struct_0(X44),u1_struct_0(X43),X46,esk2_5(X43,X44,X45,X46,X47))!=k1_funct_1(X47,esk2_5(X43,X44,X45,X46,X47))|r2_funct_2(u1_struct_0(X45),u1_struct_0(X43),k2_tmap_1(X44,X43,X46,X45),X47)|(~v1_funct_1(X47)|~v1_funct_2(X47,u1_struct_0(X45),u1_struct_0(X43))|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X43)))))|(~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X43))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X43)))))|(v2_struct_0(X45)|~m1_pre_topc(X45,X44))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44))|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tmap_1])])])])])])).
% 0.19/0.39  cnf(c_0_70, negated_conjecture, (k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0)=k4_tmap_1(esk3_0,esk4_0)|~m1_subset_1(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))|~v1_funct_2(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~v1_funct_1(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_40]), c_0_37]), c_0_41])])).
% 0.19/0.39  cnf(c_0_71, negated_conjecture, (v1_funct_2(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),X1),u1_struct_0(X1),u1_struct_0(esk3_0))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_61]), c_0_38])])).
% 0.19/0.39  cnf(c_0_72, negated_conjecture, (v1_funct_1(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),X1))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_61]), c_0_38])])).
% 0.19/0.39  cnf(c_0_73, negated_conjecture, (m1_subset_1(k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_61]), c_0_38])])).
% 0.19/0.39  cnf(c_0_74, plain, (r2_hidden(esk2_5(X1,X2,X3,X4,X5),u1_struct_0(X3))|r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.39  cnf(c_0_75, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_76, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_77, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_78, negated_conjecture, (k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0)=k4_tmap_1(esk3_0,esk4_0)|~l1_struct_0(esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), c_0_73])).
% 0.19/0.39  cnf(c_0_79, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(X1,esk3_0,X2,esk4_0),esk5_0)|r2_hidden(esk2_5(esk3_0,X1,esk4_0,X2,esk5_0),u1_struct_0(esk4_0))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))|~v1_funct_1(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_27]), c_0_28]), c_0_76]), c_0_77])]), c_0_42]), c_0_29])).
% 0.19/0.39  cnf(c_0_80, negated_conjecture, (k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0)=k4_tmap_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_61]), c_0_38])])).
% 0.19/0.39  cnf(c_0_81, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_82, plain, (m1_subset_1(esk2_5(X1,X2,X3,X4,X5),u1_struct_0(X2))|r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.39  fof(c_0_83, plain, ![X56, X57, X58]:(v2_struct_0(X56)|~v2_pre_topc(X56)|~l1_pre_topc(X56)|(v2_struct_0(X57)|~m1_pre_topc(X57,X56)|(~m1_subset_1(X58,u1_struct_0(X56))|(~r2_hidden(X58,u1_struct_0(X57))|k1_funct_1(k4_tmap_1(X56,X57),X58)=X58)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t95_tmap_1])])])])).
% 0.19/0.39  cnf(c_0_84, negated_conjecture, (r2_hidden(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))|~m1_pre_topc(esk4_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_37]), c_0_80]), c_0_38]), c_0_39]), c_0_40]), c_0_41])]), c_0_42]), c_0_81])).
% 0.19/0.39  fof(c_0_85, plain, ![X24, X25, X26]:(v2_struct_0(X24)|~l1_pre_topc(X24)|(v2_struct_0(X25)|~m1_pre_topc(X25,X24)|(~m1_subset_1(X26,u1_struct_0(X25))|m1_subset_1(X26,u1_struct_0(X24))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.19/0.39  cnf(c_0_86, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(X1,esk3_0,X2,esk4_0),esk5_0)|m1_subset_1(esk2_5(esk3_0,X1,esk4_0,X2,esk5_0),u1_struct_0(X1))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))|~v1_funct_1(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_75]), c_0_27]), c_0_28]), c_0_76]), c_0_77])]), c_0_42]), c_0_29])).
% 0.19/0.39  fof(c_0_87, plain, ![X11, X12, X13, X14]:(v1_xboole_0(X11)|~v1_funct_1(X13)|~v1_funct_2(X13,X11,X12)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|~m1_subset_1(X14,X11)|k3_funct_2(X11,X12,X13,X14)=k1_funct_1(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.19/0.39  cnf(c_0_88, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k1_funct_1(k4_tmap_1(X1,X2),X3)=X3|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.19/0.39  cnf(c_0_89, negated_conjecture, (r2_hidden(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_46]), c_0_38])])).
% 0.19/0.39  cnf(c_0_90, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.19/0.39  cnf(c_0_91, negated_conjecture, (m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))|~m1_pre_topc(esk4_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_37]), c_0_80]), c_0_38]), c_0_39]), c_0_40]), c_0_41])]), c_0_42]), c_0_81])).
% 0.19/0.39  cnf(c_0_92, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.19/0.39  fof(c_0_93, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.39  cnf(c_0_94, negated_conjecture, (k1_funct_1(k4_tmap_1(X1,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0))=esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_42])).
% 0.19/0.39  cnf(c_0_95, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_26]), c_0_27])]), c_0_42]), c_0_29])).
% 0.19/0.39  cnf(c_0_96, negated_conjecture, (m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_46]), c_0_38])])).
% 0.19/0.39  cnf(c_0_97, negated_conjecture, (k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),X1)=k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)|v1_xboole_0(u1_struct_0(esk4_0))|~m1_subset_1(k4_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_37]), c_0_41])])).
% 0.19/0.39  cnf(c_0_98, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.19/0.39  cnf(c_0_99, negated_conjecture, (k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0))=esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)|~m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_26]), c_0_27]), c_0_28])]), c_0_29])).
% 0.19/0.39  cnf(c_0_100, negated_conjecture, (m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.19/0.39  cnf(c_0_101, negated_conjecture, (X1=k1_funct_1(esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_102, negated_conjecture, (k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),X1)=k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)|v1_xboole_0(u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_40])])).
% 0.19/0.39  cnf(c_0_103, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_98, c_0_89])).
% 0.19/0.39  cnf(c_0_104, negated_conjecture, (k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0))=esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_100])])).
% 0.19/0.39  cnf(c_0_105, negated_conjecture, (k1_funct_1(esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0))=esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)|~m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_101, c_0_89])).
% 0.19/0.39  cnf(c_0_106, plain, (r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k2_tmap_1(X1,X2,X3,X4),X5)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_5(X2,X1,X4,X3,X5))!=k1_funct_1(X5,esk2_5(X2,X1,X4,X3,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.39  cnf(c_0_107, negated_conjecture, (k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0))=esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_96]), c_0_103]), c_0_104])).
% 0.19/0.39  cnf(c_0_108, negated_conjecture, (k1_funct_1(esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0))=esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_100])])).
% 0.19/0.39  cnf(c_0_109, negated_conjecture, (~m1_pre_topc(esk4_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_80]), c_0_108]), c_0_27]), c_0_38]), c_0_28]), c_0_39]), c_0_76]), c_0_40]), c_0_75]), c_0_37]), c_0_77]), c_0_41])]), c_0_42]), c_0_29]), c_0_81])).
% 0.19/0.39  cnf(c_0_110, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_46]), c_0_38])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 111
% 0.19/0.39  # Proof object clause steps            : 76
% 0.19/0.39  # Proof object formula steps           : 35
% 0.19/0.39  # Proof object conjectures             : 56
% 0.19/0.39  # Proof object clause conjectures      : 53
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 32
% 0.19/0.39  # Proof object initial formulas used   : 17
% 0.19/0.39  # Proof object generating inferences   : 40
% 0.19/0.39  # Proof object simplifying inferences  : 154
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 17
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 34
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 34
% 0.19/0.39  # Processed clauses                    : 202
% 0.19/0.39  # ...of these trivial                  : 2
% 0.19/0.39  # ...subsumed                          : 7
% 0.19/0.39  # ...remaining for further processing  : 193
% 0.19/0.39  # Other redundant clauses eliminated   : 1
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 28
% 0.19/0.39  # Backward-rewritten                   : 21
% 0.19/0.39  # Generated clauses                    : 196
% 0.19/0.39  # ...of the previous two non-trivial   : 185
% 0.19/0.39  # Contextual simplify-reflections      : 31
% 0.19/0.39  # Paramodulations                      : 195
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 1
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 109
% 0.19/0.39  #    Positive orientable unit clauses  : 32
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 5
% 0.19/0.39  #    Non-unit-clauses                  : 72
% 0.19/0.39  # Current number of unprocessed clauses: 51
% 0.19/0.39  # ...number of literals in the above   : 463
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 83
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 5334
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 564
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 65
% 0.19/0.39  # Unit Clause-clause subsumption calls : 300
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 53
% 0.19/0.39  # BW rewrite match successes           : 6
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 15485
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.055 s
% 0.19/0.39  # System time              : 0.003 s
% 0.19/0.39  # Total time               : 0.058 s
% 0.19/0.39  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
