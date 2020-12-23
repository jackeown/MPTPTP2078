%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:09 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 (6655 expanded)
%              Number of clauses        :   74 (2119 expanded)
%              Number of leaves         :   16 (1657 expanded)
%              Depth                    :   19
%              Number of atoms          :  661 (55472 expanded)
%              Number of equality atoms :   39 (3828 expanded)
%              Maximal formula depth    :   24 (   7 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tmap_1)).

fof(dt_k4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_funct_1(k4_tmap_1(X1,X2))
        & v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
        & m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(t7_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X2)
             => m1_pre_topc(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,plain,(
    ! [X42,X43] :
      ( ( v1_funct_1(k4_tmap_1(X42,X43))
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42)
        | ~ m1_pre_topc(X43,X42) )
      & ( v1_funct_2(k4_tmap_1(X42,X43),u1_struct_0(X43),u1_struct_0(X42))
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42)
        | ~ m1_pre_topc(X43,X42) )
      & ( m1_subset_1(k4_tmap_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),u1_struct_0(X42))))
        | v2_struct_0(X42)
        | ~ v2_pre_topc(X42)
        | ~ l1_pre_topc(X42)
        | ~ m1_pre_topc(X43,X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).

fof(c_0_18,negated_conjecture,(
    ! [X64] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk3_0)
      & v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
      & ( ~ m1_subset_1(X64,u1_struct_0(esk3_0))
        | ~ r2_hidden(X64,u1_struct_0(esk4_0))
        | X64 = k1_funct_1(esk5_0,X64) )
      & ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])).

fof(c_0_19,plain,(
    ! [X37,X38,X39,X40,X41] :
      ( ( v1_funct_1(k3_tmap_1(X37,X38,X39,X40,X41))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38)
        | ~ m1_pre_topc(X39,X37)
        | ~ m1_pre_topc(X40,X37)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X38))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X38)))) )
      & ( v1_funct_2(k3_tmap_1(X37,X38,X39,X40,X41),u1_struct_0(X40),u1_struct_0(X38))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38)
        | ~ m1_pre_topc(X39,X37)
        | ~ m1_pre_topc(X40,X37)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X38))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X38)))) )
      & ( m1_subset_1(k3_tmap_1(X37,X38,X39,X40,X41),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X38))))
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38)
        | ~ m1_pre_topc(X39,X37)
        | ~ m1_pre_topc(X40,X37)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X38))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X38)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).

cnf(c_0_20,plain,
    ( v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v1_funct_1(k4_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_27,plain,(
    ! [X51,X52,X53,X54] :
      ( v2_struct_0(X51)
      | ~ v2_pre_topc(X51)
      | ~ l1_pre_topc(X51)
      | v2_struct_0(X52)
      | ~ v2_pre_topc(X52)
      | ~ l1_pre_topc(X52)
      | v2_struct_0(X53)
      | ~ m1_pre_topc(X53,X51)
      | ~ v1_funct_1(X54)
      | ~ v1_funct_2(X54,u1_struct_0(X53),u1_struct_0(X52))
      | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X52))))
      | r2_funct_2(u1_struct_0(X53),u1_struct_0(X52),X54,k3_tmap_1(X51,X52,X53,X53,X54)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_tmap_1])])])])).

fof(c_0_28,plain,(
    ! [X23,X24] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_pre_topc(X24,X23)
      | l1_pre_topc(X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_29,plain,(
    ! [X21,X22] :
      ( ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | ~ m1_pre_topc(X22,X21)
      | v2_pre_topc(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_30,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_2(k4_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(k4_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(k4_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

fof(c_0_34,plain,(
    ! [X44] :
      ( ~ l1_pre_topc(X44)
      | m1_pre_topc(X44,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_35,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_37,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k3_tmap_1(X1,esk3_0,esk4_0,X2,k4_tmap_1(esk3_0,esk4_0)))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_22]),c_0_23]),c_0_32]),c_0_33])]),c_0_24])).

cnf(c_0_40,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_42,plain,(
    ! [X32,X33,X34,X35,X36] :
      ( v2_struct_0(X32)
      | ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | v2_struct_0(X33)
      | ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | ~ m1_pre_topc(X34,X32)
      | ~ m1_pre_topc(X35,X32)
      | ~ v1_funct_1(X36)
      | ~ v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X33))
      | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X33))))
      | ~ m1_pre_topc(X35,X34)
      | k3_tmap_1(X32,X33,X34,X35,X36) = k2_partfun1(u1_struct_0(X34),u1_struct_0(X33),X36,u1_struct_0(X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_43,plain,(
    ! [X55,X56,X57] :
      ( ~ v2_pre_topc(X55)
      | ~ l1_pre_topc(X55)
      | ~ m1_pre_topc(X56,X55)
      | ~ m1_pre_topc(X57,X56)
      | m1_pre_topc(X57,X55) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_44,plain,(
    ! [X28,X29,X30,X31] :
      ( v2_struct_0(X28)
      | ~ v2_pre_topc(X28)
      | ~ l1_pre_topc(X28)
      | v2_struct_0(X29)
      | ~ v2_pre_topc(X29)
      | ~ l1_pre_topc(X29)
      | ~ v1_funct_1(X30)
      | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))
      | ~ m1_pre_topc(X31,X28)
      | k2_tmap_1(X28,X29,X30,X31) = k2_partfun1(u1_struct_0(X28),u1_struct_0(X29),X30,u1_struct_0(X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

fof(c_0_45,plain,(
    ! [X17,X18,X19,X20] :
      ( ( ~ r2_funct_2(X17,X18,X19,X20)
        | X19 = X20
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,X17,X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( X19 != X20
        | r2_funct_2(X17,X18,X19,X20)
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,X17,X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_46,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),k3_tmap_1(X1,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0)))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_31]),c_0_22]),c_0_23]),c_0_32]),c_0_33])]),c_0_36]),c_0_24])).

cnf(c_0_47,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_21]),c_0_22])])).

cnf(c_0_48,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_49,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k3_tmap_1(X1,esk3_0,esk4_0,X1,k4_tmap_1(esk3_0,esk4_0)))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k3_tmap_1(X1,esk3_0,esk4_0,X2,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(X2),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_31]),c_0_22]),c_0_23]),c_0_32]),c_0_33])]),c_0_24])).

cnf(c_0_51,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_52,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_40]),c_0_47]),c_0_48])]),c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_40]),c_0_47]),c_0_48])]),c_0_36])).

cnf(c_0_58,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k3_tmap_1(X1,esk3_0,esk4_0,X1,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_40])).

cnf(c_0_59,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_tmap_1(X1,esk3_0,esk4_0,X2,k4_tmap_1(esk3_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk3_0))))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_31]),c_0_22]),c_0_23]),c_0_32]),c_0_33])]),c_0_24])).

cnf(c_0_60,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),u1_struct_0(X1)) = k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_31]),c_0_22]),c_0_47]),c_0_23]),c_0_48]),c_0_32]),c_0_33])]),c_0_24]),c_0_36])).

cnf(c_0_62,negated_conjecture,
    ( k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0)) = k4_tmap_1(esk3_0,esk4_0)
    | ~ v1_funct_2(k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_31]),c_0_57]),c_0_32]),c_0_33])])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_40]),c_0_47]),c_0_48])]),c_0_36])).

cnf(c_0_64,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_tmap_1(X1,esk3_0,esk4_0,X1,k4_tmap_1(esk3_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_40])).

fof(c_0_65,plain,(
    ! [X45,X46,X47,X48,X49] :
      ( ( m1_subset_1(esk2_5(X45,X46,X47,X48,X49),u1_struct_0(X46))
        | r2_funct_2(u1_struct_0(X47),u1_struct_0(X45),k2_tmap_1(X46,X45,X48,X47),X49)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X45))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X45))))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X45))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45))))
        | v2_struct_0(X47)
        | ~ m1_pre_topc(X47,X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46)
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) )
      & ( r2_hidden(esk2_5(X45,X46,X47,X48,X49),u1_struct_0(X47))
        | r2_funct_2(u1_struct_0(X47),u1_struct_0(X45),k2_tmap_1(X46,X45,X48,X47),X49)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X45))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X45))))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X45))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45))))
        | v2_struct_0(X47)
        | ~ m1_pre_topc(X47,X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46)
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) )
      & ( k3_funct_2(u1_struct_0(X46),u1_struct_0(X45),X48,esk2_5(X45,X46,X47,X48,X49)) != k1_funct_1(X49,esk2_5(X45,X46,X47,X48,X49))
        | r2_funct_2(u1_struct_0(X47),u1_struct_0(X45),k2_tmap_1(X46,X45,X48,X47),X49)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X45))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X45))))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X45))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45))))
        | v2_struct_0(X47)
        | ~ m1_pre_topc(X47,X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46)
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tmap_1])])])])])])).

cnf(c_0_66,negated_conjecture,
    ( k3_tmap_1(X1,esk3_0,esk4_0,X2,k4_tmap_1(esk3_0,esk4_0)) = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_31]),c_0_22]),c_0_23]),c_0_32]),c_0_33])]),c_0_24])).

cnf(c_0_67,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0)) = k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_40]),c_0_47])])).

cnf(c_0_68,negated_conjecture,
    ( k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0)) = k4_tmap_1(esk3_0,esk4_0)
    | ~ m1_subset_1(k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_40]),c_0_47]),c_0_48])]),c_0_36])).

cnf(c_0_70,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_74,negated_conjecture,
    ( k3_tmap_1(X1,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0)) = k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_40]),c_0_67]),c_0_47])])).

cnf(c_0_75,negated_conjecture,
    ( k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0)) = k4_tmap_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69])])).

cnf(c_0_76,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(X1,esk3_0,X2,esk4_0),esk5_0)
    | r2_hidden(esk2_5(esk3_0,X1,esk4_0,X2,esk5_0),u1_struct_0(esk4_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_22]),c_0_23]),c_0_72]),c_0_73])]),c_0_36]),c_0_24])).

cnf(c_0_77,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0) = k4_tmap_1(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_40]),c_0_75]),c_0_47]),c_0_48])]),c_0_36])).

cnf(c_0_78,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_79,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_80,plain,(
    ! [X58,X59,X60] :
      ( v2_struct_0(X58)
      | ~ v2_pre_topc(X58)
      | ~ l1_pre_topc(X58)
      | v2_struct_0(X59)
      | ~ m1_pre_topc(X59,X58)
      | ~ m1_subset_1(X60,u1_struct_0(X58))
      | ~ r2_hidden(X60,u1_struct_0(X59))
      | k1_funct_1(k4_tmap_1(X58,X59),X60) = X60 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t95_tmap_1])])])])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))
    | ~ m1_pre_topc(esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_31]),c_0_77]),c_0_47]),c_0_48]),c_0_32]),c_0_33])]),c_0_36]),c_0_78])).

fof(c_0_82,plain,(
    ! [X25,X26,X27] :
      ( v2_struct_0(X25)
      | ~ l1_pre_topc(X25)
      | v2_struct_0(X26)
      | ~ m1_pre_topc(X26,X25)
      | ~ m1_subset_1(X27,u1_struct_0(X26))
      | m1_subset_1(X27,u1_struct_0(X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_83,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(X1,esk3_0,X2,esk4_0),esk5_0)
    | m1_subset_1(esk2_5(esk3_0,X1,esk4_0,X2,esk5_0),u1_struct_0(X1))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_71]),c_0_22]),c_0_23]),c_0_72]),c_0_73])]),c_0_36]),c_0_24])).

cnf(c_0_84,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_funct_1(k4_tmap_1(X1,X2),X3) = X3
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_40]),c_0_47])])).

cnf(c_0_86,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))
    | ~ m1_pre_topc(esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_31]),c_0_77]),c_0_47]),c_0_48]),c_0_32]),c_0_33])]),c_0_36]),c_0_78])).

fof(c_0_88,plain,(
    ! [X13,X14,X15,X16] :
      ( v1_xboole_0(X13)
      | ~ v1_funct_1(X15)
      | ~ v1_funct_2(X15,X13,X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | ~ m1_subset_1(X16,X13)
      | k3_funct_2(X13,X14,X15,X16) = k1_funct_1(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

fof(c_0_89,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_90,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(X1,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)) = esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_36])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_21]),c_0_22])]),c_0_36]),c_0_24])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_40]),c_0_47])])).

cnf(c_0_93,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_94,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)) = esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | ~ m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_97,negated_conjecture,
    ( X1 = k1_funct_1(esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_98,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),X1) = k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_99,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_85])).

cnf(c_0_100,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)) = esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_96])])).

cnf(c_0_101,negated_conjecture,
    ( k1_funct_1(esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)) = esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)
    | ~ m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_85])).

cnf(c_0_102,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_103,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)) = esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_92]),c_0_99]),c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( k1_funct_1(esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)) = esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_96])])).

cnf(c_0_105,negated_conjecture,
    ( ~ m1_pre_topc(esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_77]),c_0_104]),c_0_22]),c_0_47]),c_0_23]),c_0_48]),c_0_71]),c_0_31]),c_0_72]),c_0_32]),c_0_73]),c_0_33])]),c_0_36]),c_0_24]),c_0_78])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_40]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:02:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.44  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.21/0.44  # and selection function SelectCQIPrecWNTNp.
% 0.21/0.44  #
% 0.21/0.44  # Preprocessing time       : 0.030 s
% 0.21/0.44  # Presaturation interreduction done
% 0.21/0.44  
% 0.21/0.44  # Proof found!
% 0.21/0.44  # SZS status Theorem
% 0.21/0.44  # SZS output start CNFRefutation
% 0.21/0.44  fof(t96_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_tmap_1)).
% 0.21/0.44  fof(dt_k4_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k4_tmap_1(X1,X2))&v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 0.21/0.44  fof(dt_k3_tmap_1, axiom, ![X1, X2, X3, X4, X5]:(((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&m1_pre_topc(X3,X1))&m1_pre_topc(X4,X1))&v1_funct_1(X5))&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>((v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))&v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 0.21/0.44  fof(t74_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 0.21/0.44  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.21/0.44  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.21/0.44  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.21/0.44  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.21/0.44  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.21/0.44  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.21/0.44  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.21/0.44  fof(t59_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>(![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(r2_hidden(X6,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6)=k1_funct_1(X5,X6)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tmap_1)).
% 0.21/0.44  fof(t95_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,u1_struct_0(X2))=>k1_funct_1(k4_tmap_1(X1,X2),X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_tmap_1)).
% 0.21/0.44  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.21/0.44  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.21/0.44  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.21/0.44  fof(c_0_16, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3)))))), inference(assume_negation,[status(cth)],[t96_tmap_1])).
% 0.21/0.44  fof(c_0_17, plain, ![X42, X43]:(((v1_funct_1(k4_tmap_1(X42,X43))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)|~m1_pre_topc(X43,X42)))&(v1_funct_2(k4_tmap_1(X42,X43),u1_struct_0(X43),u1_struct_0(X42))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)|~m1_pre_topc(X43,X42))))&(m1_subset_1(k4_tmap_1(X42,X43),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),u1_struct_0(X42))))|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)|~m1_pre_topc(X43,X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).
% 0.21/0.44  fof(c_0_18, negated_conjecture, ![X64]:(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))))&((~m1_subset_1(X64,u1_struct_0(esk3_0))|(~r2_hidden(X64,u1_struct_0(esk4_0))|X64=k1_funct_1(esk5_0,X64)))&~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])).
% 0.21/0.44  fof(c_0_19, plain, ![X37, X38, X39, X40, X41]:(((v1_funct_1(k3_tmap_1(X37,X38,X39,X40,X41))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)|~m1_pre_topc(X39,X37)|~m1_pre_topc(X40,X37)|~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X38))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X38))))))&(v1_funct_2(k3_tmap_1(X37,X38,X39,X40,X41),u1_struct_0(X40),u1_struct_0(X38))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)|~m1_pre_topc(X39,X37)|~m1_pre_topc(X40,X37)|~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X38))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X38)))))))&(m1_subset_1(k3_tmap_1(X37,X38,X39,X40,X41),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X38))))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)|~m1_pre_topc(X39,X37)|~m1_pre_topc(X40,X37)|~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X38))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X38))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).
% 0.21/0.44  cnf(c_0_20, plain, (v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.44  cnf(c_0_21, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.44  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.44  cnf(c_0_23, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.44  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.44  cnf(c_0_25, plain, (v1_funct_1(k4_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.44  cnf(c_0_26, plain, (m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.44  fof(c_0_27, plain, ![X51, X52, X53, X54]:(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51)|(v2_struct_0(X52)|~v2_pre_topc(X52)|~l1_pre_topc(X52)|(v2_struct_0(X53)|~m1_pre_topc(X53,X51)|(~v1_funct_1(X54)|~v1_funct_2(X54,u1_struct_0(X53),u1_struct_0(X52))|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X52))))|r2_funct_2(u1_struct_0(X53),u1_struct_0(X52),X54,k3_tmap_1(X51,X52,X53,X53,X54)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_tmap_1])])])])).
% 0.21/0.44  fof(c_0_28, plain, ![X23, X24]:(~l1_pre_topc(X23)|(~m1_pre_topc(X24,X23)|l1_pre_topc(X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.21/0.44  fof(c_0_29, plain, ![X21, X22]:(~v2_pre_topc(X21)|~l1_pre_topc(X21)|(~m1_pre_topc(X22,X21)|v2_pre_topc(X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.21/0.44  cnf(c_0_30, plain, (v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.44  cnf(c_0_31, negated_conjecture, (v1_funct_2(k4_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.21/0.44  cnf(c_0_32, negated_conjecture, (v1_funct_1(k4_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.21/0.44  cnf(c_0_33, negated_conjecture, (m1_subset_1(k4_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.21/0.44  fof(c_0_34, plain, ![X44]:(~l1_pre_topc(X44)|m1_pre_topc(X44,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.21/0.44  cnf(c_0_35, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.44  cnf(c_0_36, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.44  cnf(c_0_37, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.44  cnf(c_0_38, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.44  cnf(c_0_39, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k3_tmap_1(X1,esk3_0,esk4_0,X2,k4_tmap_1(esk3_0,esk4_0)))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_22]), c_0_23]), c_0_32]), c_0_33])]), c_0_24])).
% 0.21/0.44  cnf(c_0_40, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.44  cnf(c_0_41, plain, (v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.44  fof(c_0_42, plain, ![X32, X33, X34, X35, X36]:(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|(~m1_pre_topc(X34,X32)|(~m1_pre_topc(X35,X32)|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X33))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X33))))|(~m1_pre_topc(X35,X34)|k3_tmap_1(X32,X33,X34,X35,X36)=k2_partfun1(u1_struct_0(X34),u1_struct_0(X33),X36,u1_struct_0(X35)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.21/0.44  fof(c_0_43, plain, ![X55, X56, X57]:(~v2_pre_topc(X55)|~l1_pre_topc(X55)|(~m1_pre_topc(X56,X55)|(~m1_pre_topc(X57,X56)|m1_pre_topc(X57,X55)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.21/0.44  fof(c_0_44, plain, ![X28, X29, X30, X31]:(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))|(~m1_pre_topc(X31,X28)|k2_tmap_1(X28,X29,X30,X31)=k2_partfun1(u1_struct_0(X28),u1_struct_0(X29),X30,u1_struct_0(X31)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.21/0.44  fof(c_0_45, plain, ![X17, X18, X19, X20]:((~r2_funct_2(X17,X18,X19,X20)|X19=X20|(~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|~v1_funct_1(X20)|~v1_funct_2(X20,X17,X18)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))&(X19!=X20|r2_funct_2(X17,X18,X19,X20)|(~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|~v1_funct_1(X20)|~v1_funct_2(X20,X17,X18)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.21/0.44  cnf(c_0_46, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),k3_tmap_1(X1,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0)))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_31]), c_0_22]), c_0_23]), c_0_32]), c_0_33])]), c_0_36]), c_0_24])).
% 0.21/0.44  cnf(c_0_47, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_21]), c_0_22])])).
% 0.21/0.44  cnf(c_0_48, negated_conjecture, (v2_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_21]), c_0_22]), c_0_23])])).
% 0.21/0.44  cnf(c_0_49, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k3_tmap_1(X1,esk3_0,esk4_0,X1,k4_tmap_1(esk3_0,esk4_0)))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.44  cnf(c_0_50, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k3_tmap_1(X1,esk3_0,esk4_0,X2,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(X2),u1_struct_0(esk3_0))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_31]), c_0_22]), c_0_23]), c_0_32]), c_0_33])]), c_0_24])).
% 0.21/0.44  cnf(c_0_51, plain, (m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.44  cnf(c_0_52, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.44  cnf(c_0_53, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.44  cnf(c_0_54, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.44  cnf(c_0_55, plain, (X3=X4|~r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.44  cnf(c_0_56, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_40]), c_0_47]), c_0_48])]), c_0_36])).
% 0.21/0.44  cnf(c_0_57, negated_conjecture, (v1_funct_1(k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_40]), c_0_47]), c_0_48])]), c_0_36])).
% 0.21/0.44  cnf(c_0_58, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k3_tmap_1(X1,esk3_0,esk4_0,X1,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(X1),u1_struct_0(esk3_0))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_50, c_0_40])).
% 0.21/0.44  cnf(c_0_59, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k3_tmap_1(X1,esk3_0,esk4_0,X2,k4_tmap_1(esk3_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk3_0))))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_31]), c_0_22]), c_0_23]), c_0_32]), c_0_33])]), c_0_24])).
% 0.21/0.44  cnf(c_0_60, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(csr,[status(thm)],[c_0_52, c_0_53])).
% 0.21/0.44  cnf(c_0_61, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),u1_struct_0(X1))=k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),X1)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_31]), c_0_22]), c_0_47]), c_0_23]), c_0_48]), c_0_32]), c_0_33])]), c_0_24]), c_0_36])).
% 0.21/0.44  cnf(c_0_62, negated_conjecture, (k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0))=k4_tmap_1(esk3_0,esk4_0)|~v1_funct_2(k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~m1_subset_1(k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_31]), c_0_57]), c_0_32]), c_0_33])])).
% 0.21/0.44  cnf(c_0_63, negated_conjecture, (v1_funct_2(k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_40]), c_0_47]), c_0_48])]), c_0_36])).
% 0.21/0.44  cnf(c_0_64, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k3_tmap_1(X1,esk3_0,esk4_0,X1,k4_tmap_1(esk3_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_59, c_0_40])).
% 0.21/0.44  fof(c_0_65, plain, ![X45, X46, X47, X48, X49]:((m1_subset_1(esk2_5(X45,X46,X47,X48,X49),u1_struct_0(X46))|r2_funct_2(u1_struct_0(X47),u1_struct_0(X45),k2_tmap_1(X46,X45,X48,X47),X49)|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X45))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X45)))))|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X45))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45)))))|(v2_struct_0(X47)|~m1_pre_topc(X47,X46))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46))|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)))&((r2_hidden(esk2_5(X45,X46,X47,X48,X49),u1_struct_0(X47))|r2_funct_2(u1_struct_0(X47),u1_struct_0(X45),k2_tmap_1(X46,X45,X48,X47),X49)|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X45))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X45)))))|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X45))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45)))))|(v2_struct_0(X47)|~m1_pre_topc(X47,X46))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46))|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)))&(k3_funct_2(u1_struct_0(X46),u1_struct_0(X45),X48,esk2_5(X45,X46,X47,X48,X49))!=k1_funct_1(X49,esk2_5(X45,X46,X47,X48,X49))|r2_funct_2(u1_struct_0(X47),u1_struct_0(X45),k2_tmap_1(X46,X45,X48,X47),X49)|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X45))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X45)))))|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X45))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45)))))|(v2_struct_0(X47)|~m1_pre_topc(X47,X46))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46))|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tmap_1])])])])])])).
% 0.21/0.44  cnf(c_0_66, negated_conjecture, (k3_tmap_1(X1,esk3_0,esk4_0,X2,k4_tmap_1(esk3_0,esk4_0))=k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk4_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_31]), c_0_22]), c_0_23]), c_0_32]), c_0_33])]), c_0_24])).
% 0.21/0.44  cnf(c_0_67, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0))=k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_40]), c_0_47])])).
% 0.21/0.44  cnf(c_0_68, negated_conjecture, (k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0))=k4_tmap_1(esk3_0,esk4_0)|~m1_subset_1(k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63])])).
% 0.21/0.44  cnf(c_0_69, negated_conjecture, (m1_subset_1(k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_40]), c_0_47]), c_0_48])]), c_0_36])).
% 0.21/0.44  cnf(c_0_70, plain, (r2_hidden(esk2_5(X1,X2,X3,X4,X5),u1_struct_0(X3))|r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.21/0.44  cnf(c_0_71, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.44  cnf(c_0_72, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.44  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.44  cnf(c_0_74, negated_conjecture, (k3_tmap_1(X1,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0))=k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0)|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_40]), c_0_67]), c_0_47])])).
% 0.21/0.44  cnf(c_0_75, negated_conjecture, (k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0))=k4_tmap_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69])])).
% 0.21/0.44  cnf(c_0_76, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(X1,esk3_0,X2,esk4_0),esk5_0)|r2_hidden(esk2_5(esk3_0,X1,esk4_0,X2,esk5_0),u1_struct_0(esk4_0))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_22]), c_0_23]), c_0_72]), c_0_73])]), c_0_36]), c_0_24])).
% 0.21/0.44  cnf(c_0_77, negated_conjecture, (k2_tmap_1(esk4_0,esk3_0,k4_tmap_1(esk3_0,esk4_0),esk4_0)=k4_tmap_1(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_40]), c_0_75]), c_0_47]), c_0_48])]), c_0_36])).
% 0.21/0.44  cnf(c_0_78, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.44  cnf(c_0_79, plain, (m1_subset_1(esk2_5(X1,X2,X3,X4,X5),u1_struct_0(X2))|r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.21/0.44  fof(c_0_80, plain, ![X58, X59, X60]:(v2_struct_0(X58)|~v2_pre_topc(X58)|~l1_pre_topc(X58)|(v2_struct_0(X59)|~m1_pre_topc(X59,X58)|(~m1_subset_1(X60,u1_struct_0(X58))|(~r2_hidden(X60,u1_struct_0(X59))|k1_funct_1(k4_tmap_1(X58,X59),X60)=X60)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t95_tmap_1])])])])).
% 0.21/0.44  cnf(c_0_81, negated_conjecture, (r2_hidden(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))|~m1_pre_topc(esk4_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_31]), c_0_77]), c_0_47]), c_0_48]), c_0_32]), c_0_33])]), c_0_36]), c_0_78])).
% 0.21/0.44  fof(c_0_82, plain, ![X25, X26, X27]:(v2_struct_0(X25)|~l1_pre_topc(X25)|(v2_struct_0(X26)|~m1_pre_topc(X26,X25)|(~m1_subset_1(X27,u1_struct_0(X26))|m1_subset_1(X27,u1_struct_0(X25))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.21/0.44  cnf(c_0_83, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(X1,esk3_0,X2,esk4_0),esk5_0)|m1_subset_1(esk2_5(esk3_0,X1,esk4_0,X2,esk5_0),u1_struct_0(X1))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_71]), c_0_22]), c_0_23]), c_0_72]), c_0_73])]), c_0_36]), c_0_24])).
% 0.21/0.44  cnf(c_0_84, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k1_funct_1(k4_tmap_1(X1,X2),X3)=X3|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.21/0.44  cnf(c_0_85, negated_conjecture, (r2_hidden(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_40]), c_0_47])])).
% 0.21/0.44  cnf(c_0_86, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.21/0.44  cnf(c_0_87, negated_conjecture, (m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))|~m1_pre_topc(esk4_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_31]), c_0_77]), c_0_47]), c_0_48]), c_0_32]), c_0_33])]), c_0_36]), c_0_78])).
% 0.21/0.44  fof(c_0_88, plain, ![X13, X14, X15, X16]:(v1_xboole_0(X13)|~v1_funct_1(X15)|~v1_funct_2(X15,X13,X14)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|~m1_subset_1(X16,X13)|k3_funct_2(X13,X14,X15,X16)=k1_funct_1(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.21/0.44  fof(c_0_89, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.21/0.44  cnf(c_0_90, negated_conjecture, (k1_funct_1(k4_tmap_1(X1,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0))=esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_36])).
% 0.21/0.44  cnf(c_0_91, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_21]), c_0_22])]), c_0_36]), c_0_24])).
% 0.21/0.44  cnf(c_0_92, negated_conjecture, (m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_40]), c_0_47])])).
% 0.21/0.44  cnf(c_0_93, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.21/0.44  cnf(c_0_94, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.21/0.44  cnf(c_0_95, negated_conjecture, (k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0))=esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)|~m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.21/0.44  cnf(c_0_96, negated_conjecture, (m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.21/0.44  cnf(c_0_97, negated_conjecture, (X1=k1_funct_1(esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.44  cnf(c_0_98, negated_conjecture, (k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),X1)=k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)|v1_xboole_0(u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_31]), c_0_32]), c_0_33])])).
% 0.21/0.44  cnf(c_0_99, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_94, c_0_85])).
% 0.21/0.44  cnf(c_0_100, negated_conjecture, (k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0))=esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_96])])).
% 0.21/0.44  cnf(c_0_101, negated_conjecture, (k1_funct_1(esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0))=esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)|~m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_97, c_0_85])).
% 0.21/0.44  cnf(c_0_102, plain, (r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k2_tmap_1(X1,X2,X3,X4),X5)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_5(X2,X1,X4,X3,X5))!=k1_funct_1(X5,esk2_5(X2,X1,X4,X3,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.21/0.44  cnf(c_0_103, negated_conjecture, (k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0))=esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_92]), c_0_99]), c_0_100])).
% 0.21/0.44  cnf(c_0_104, negated_conjecture, (k1_funct_1(esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0))=esk2_5(esk3_0,esk4_0,esk4_0,k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_96])])).
% 0.21/0.44  cnf(c_0_105, negated_conjecture, (~m1_pre_topc(esk4_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_77]), c_0_104]), c_0_22]), c_0_47]), c_0_23]), c_0_48]), c_0_71]), c_0_31]), c_0_72]), c_0_32]), c_0_73]), c_0_33])]), c_0_36]), c_0_24]), c_0_78])).
% 0.21/0.44  cnf(c_0_106, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_40]), c_0_47])]), ['proof']).
% 0.21/0.44  # SZS output end CNFRefutation
% 0.21/0.44  # Proof object total steps             : 107
% 0.21/0.44  # Proof object clause steps            : 74
% 0.21/0.44  # Proof object formula steps           : 33
% 0.21/0.44  # Proof object conjectures             : 55
% 0.21/0.44  # Proof object clause conjectures      : 52
% 0.21/0.44  # Proof object formula conjectures     : 3
% 0.21/0.44  # Proof object initial clauses used    : 31
% 0.21/0.44  # Proof object initial formulas used   : 16
% 0.21/0.44  # Proof object generating inferences   : 38
% 0.21/0.44  # Proof object simplifying inferences  : 163
% 0.21/0.44  # Training examples: 0 positive, 0 negative
% 0.21/0.44  # Parsed axioms                        : 17
% 0.21/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.44  # Initial clauses                      : 34
% 0.21/0.44  # Removed in clause preprocessing      : 0
% 0.21/0.44  # Initial clauses in saturation        : 34
% 0.21/0.44  # Processed clauses                    : 437
% 0.21/0.44  # ...of these trivial                  : 9
% 0.21/0.44  # ...subsumed                          : 9
% 0.21/0.44  # ...remaining for further processing  : 419
% 0.21/0.44  # Other redundant clauses eliminated   : 1
% 0.21/0.44  # Clauses deleted for lack of memory   : 0
% 0.21/0.44  # Backward-subsumed                    : 15
% 0.21/0.44  # Backward-rewritten                   : 98
% 0.21/0.44  # Generated clauses                    : 616
% 0.21/0.44  # ...of the previous two non-trivial   : 634
% 0.21/0.44  # Contextual simplify-reflections      : 35
% 0.21/0.44  # Paramodulations                      : 615
% 0.21/0.44  # Factorizations                       : 0
% 0.21/0.44  # Equation resolutions                 : 1
% 0.21/0.44  # Propositional unsat checks           : 0
% 0.21/0.44  #    Propositional check models        : 0
% 0.21/0.44  #    Propositional check unsatisfiable : 0
% 0.21/0.44  #    Propositional clauses             : 0
% 0.21/0.44  #    Propositional clauses after purity: 0
% 0.21/0.44  #    Propositional unsat core size     : 0
% 0.21/0.44  #    Propositional preprocessing time  : 0.000
% 0.21/0.44  #    Propositional encoding time       : 0.000
% 0.21/0.44  #    Propositional solver time         : 0.000
% 0.21/0.44  #    Success case prop preproc time    : 0.000
% 0.21/0.44  #    Success case prop encoding time   : 0.000
% 0.21/0.44  #    Success case prop solver time     : 0.000
% 0.21/0.44  # Current number of processed clauses  : 271
% 0.21/0.44  #    Positive orientable unit clauses  : 97
% 0.21/0.44  #    Positive unorientable unit clauses: 0
% 0.21/0.44  #    Negative unit clauses             : 5
% 0.21/0.44  #    Non-unit-clauses                  : 169
% 0.21/0.44  # Current number of unprocessed clauses: 214
% 0.21/0.44  # ...number of literals in the above   : 1089
% 0.21/0.44  # Current number of archived formulas  : 0
% 0.21/0.44  # Current number of archived clauses   : 147
% 0.21/0.44  # Clause-clause subsumption calls (NU) : 10562
% 0.21/0.44  # Rec. Clause-clause subsumption calls : 784
% 0.21/0.44  # Non-unit clause-clause subsumptions  : 56
% 0.21/0.44  # Unit Clause-clause subsumption calls : 1615
% 0.21/0.44  # Rewrite failures with RHS unbound    : 0
% 0.21/0.44  # BW rewrite match attempts            : 403
% 0.21/0.44  # BW rewrite match successes           : 45
% 0.21/0.44  # Condensation attempts                : 0
% 0.21/0.44  # Condensation successes               : 0
% 0.21/0.44  # Termbank termtop insertions          : 45170
% 0.21/0.44  
% 0.21/0.44  # -------------------------------------------------
% 0.21/0.44  # User time                : 0.091 s
% 0.21/0.44  # System time              : 0.005 s
% 0.21/0.44  # Total time               : 0.096 s
% 0.21/0.44  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
