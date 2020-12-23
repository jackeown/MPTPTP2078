%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:00 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 760 expanded)
%              Number of clauses        :   63 ( 268 expanded)
%              Number of leaves         :   17 ( 188 expanded)
%              Depth                    :   15
%              Number of atoms          :  580 (7948 expanded)
%              Number of equality atoms :   39 ( 750 expanded)
%              Maximal formula depth    :   27 (   6 average)
%              Maximal clause size      :   90 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t88_tmap_1,conjecture,(
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
                        & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                     => ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = X4
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X4))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X3))
                               => ( ( X6 = X7
                                    & r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7) )
                                 => r1_tmap_1(X4,X2,X5,X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

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

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

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

fof(t67_tmap_1,axiom,(
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
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & v1_tsep_1(X4,X2)
                    & m1_pre_topc(X4,X2) )
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X4))
                         => ( X5 = X6
                           => ( r1_tmap_1(X2,X1,X3,X5)
                            <=> r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t35_borsuk_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(t16_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( ( v1_tsep_1(X2,X1)
                    & m1_pre_topc(X2,X1) )
                <=> v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(d1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(X1)
      <=> ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,u1_pre_topc(X1))
               => r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) )
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X1))
                      & r2_hidden(X3,u1_pre_topc(X1)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(c_0_17,negated_conjecture,(
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
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                       => ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = X4
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X4))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X3))
                                 => ( ( X6 = X7
                                      & r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7) )
                                   => r1_tmap_1(X4,X2,X5,X6) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t88_tmap_1])).

fof(c_0_18,plain,(
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

fof(c_0_19,plain,(
    ! [X23,X24] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_pre_topc(X24,X23)
      | l1_pre_topc(X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & ~ v2_struct_0(esk6_0)
    & m1_pre_topc(esk6_0,esk4_0)
    & ~ v2_struct_0(esk7_0)
    & m1_pre_topc(esk7_0,esk4_0)
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0))))
    & g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) = esk7_0
    & m1_subset_1(esk9_0,u1_struct_0(esk7_0))
    & m1_subset_1(esk10_0,u1_struct_0(esk6_0))
    & esk9_0 = esk10_0
    & r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk10_0)
    & ~ r1_tmap_1(esk7_0,esk5_0,esk8_0,esk9_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_21,plain,(
    ! [X36,X37,X38,X39,X40] :
      ( v2_struct_0(X36)
      | ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | v2_struct_0(X37)
      | ~ v2_pre_topc(X37)
      | ~ l1_pre_topc(X37)
      | ~ m1_pre_topc(X38,X36)
      | ~ m1_pre_topc(X39,X36)
      | ~ v1_funct_1(X40)
      | ~ v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X37))
      | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X37))))
      | ~ m1_pre_topc(X39,X38)
      | k3_tmap_1(X36,X37,X38,X39,X40) = k2_partfun1(u1_struct_0(X38),u1_struct_0(X37),X40,u1_struct_0(X39)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_22,plain,(
    ! [X55,X56,X57] :
      ( ~ v2_pre_topc(X55)
      | ~ l1_pre_topc(X55)
      | ~ m1_pre_topc(X56,X55)
      | ~ m1_pre_topc(X57,X56)
      | m1_pre_topc(X57,X55) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

cnf(c_0_23,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

fof(c_0_32,plain,(
    ! [X46] :
      ( ~ l1_pre_topc(X46)
      | m1_pre_topc(X46,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

fof(c_0_33,plain,(
    ! [X12,X13] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ m1_pre_topc(X13,X12)
      | v2_pre_topc(X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_34,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_38,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_41,negated_conjecture,
    ( m1_pre_topc(X1,esk7_0)
    | ~ m1_pre_topc(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_42,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_43,plain,(
    ! [X32,X33,X34,X35] :
      ( v2_struct_0(X32)
      | ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | v2_struct_0(X33)
      | ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | ~ v1_funct_1(X34)
      | ~ v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X33))
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))
      | ~ m1_pre_topc(X35,X32)
      | k2_tmap_1(X32,X33,X34,X35) = k2_partfun1(u1_struct_0(X32),u1_struct_0(X33),X34,u1_struct_0(X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_44,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_45,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( k3_tmap_1(X1,esk5_0,esk7_0,X2,esk8_0) = k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk7_0)
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_31])])).

cnf(c_0_49,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_44]),c_0_26])])).

cnf(c_0_51,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_44]),c_0_26]),c_0_46])])).

cnf(c_0_52,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_53,negated_conjecture,
    ( k3_tmap_1(X1,esk5_0,esk7_0,esk6_0,esk8_0) = k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(esk6_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(X1)) = k2_tmap_1(esk7_0,esk5_0,esk8_0,X1)
    | ~ m1_pre_topc(X1,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_50]),c_0_39]),c_0_51])]),c_0_40]),c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(esk6_0)) = k3_tmap_1(esk7_0,esk5_0,esk7_0,esk6_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_42]),c_0_50]),c_0_51])]),c_0_52])).

fof(c_0_56,plain,(
    ! [X49,X50,X51,X52,X53,X54] :
      ( ( ~ r1_tmap_1(X50,X49,X51,X53)
        | r1_tmap_1(X52,X49,k2_tmap_1(X50,X49,X51,X52),X54)
        | X53 != X54
        | ~ m1_subset_1(X54,u1_struct_0(X52))
        | ~ m1_subset_1(X53,u1_struct_0(X50))
        | v2_struct_0(X52)
        | ~ v1_tsep_1(X52,X50)
        | ~ m1_pre_topc(X52,X50)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X50),u1_struct_0(X49))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X49))))
        | v2_struct_0(X50)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50)
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49) )
      & ( ~ r1_tmap_1(X52,X49,k2_tmap_1(X50,X49,X51,X52),X54)
        | r1_tmap_1(X50,X49,X51,X53)
        | X53 != X54
        | ~ m1_subset_1(X54,u1_struct_0(X52))
        | ~ m1_subset_1(X53,u1_struct_0(X50))
        | v2_struct_0(X52)
        | ~ v1_tsep_1(X52,X50)
        | ~ m1_pre_topc(X52,X50)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X50),u1_struct_0(X49))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X49))))
        | v2_struct_0(X50)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50)
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_tmap_1])])])])])).

fof(c_0_57,plain,(
    ! [X25,X26,X27] :
      ( v2_struct_0(X25)
      | ~ l1_pre_topc(X25)
      | v2_struct_0(X26)
      | ~ m1_pre_topc(X26,X25)
      | ~ m1_subset_1(X27,u1_struct_0(X26))
      | m1_subset_1(X27,u1_struct_0(X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_58,negated_conjecture,
    ( k3_tmap_1(esk7_0,esk5_0,esk7_0,esk6_0,esk8_0) = k2_tmap_1(esk7_0,esk5_0,esk8_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_48])])).

fof(c_0_59,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_60,plain,(
    ! [X47,X48] :
      ( ~ l1_pre_topc(X47)
      | ~ m1_pre_topc(X48,X47)
      | r1_tarski(u1_struct_0(X48),u1_struct_0(X47)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

fof(c_0_61,plain,(
    ! [X28,X29] :
      ( ~ l1_pre_topc(X28)
      | ~ m1_pre_topc(X29,g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28)))
      | m1_pre_topc(X29,X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

cnf(c_0_62,plain,
    ( r1_tmap_1(X3,X2,X4,X6)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | X6 != X5
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ v1_tsep_1(X1,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_65,negated_conjecture,
    ( esk9_0 = esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_66,negated_conjecture,
    ( k3_tmap_1(X1,esk5_0,esk7_0,esk6_0,esk8_0) = k2_tmap_1(esk7_0,esk5_0,esk8_0,esk6_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_55]),c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_68,plain,(
    ! [X41,X42,X43] :
      ( ( ~ v1_tsep_1(X42,X41)
        | ~ m1_pre_topc(X42,X41)
        | v3_pre_topc(X43,X41)
        | X43 != u1_struct_0(X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ m1_pre_topc(X42,X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) )
      & ( v1_tsep_1(X42,X41)
        | ~ v3_pre_topc(X43,X41)
        | X43 != u1_struct_0(X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ m1_pre_topc(X42,X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) )
      & ( m1_pre_topc(X42,X41)
        | ~ v3_pre_topc(X43,X41)
        | X43 != u1_struct_0(X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ m1_pre_topc(X42,X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).

fof(c_0_69,plain,(
    ! [X44,X45] :
      ( ~ l1_pre_topc(X44)
      | ~ m1_pre_topc(X45,X44)
      | m1_subset_1(u1_struct_0(X45),k1_zfmisc_1(u1_struct_0(X44))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_70,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_71,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_72,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_73,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | ~ r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)
    | ~ v1_tsep_1(X5,X1)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_pre_topc(X5,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,u1_struct_0(X5)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_62]),c_0_63])).

cnf(c_0_74,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk9_0) ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_75,negated_conjecture,
    ( k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0) = k2_tmap_1(esk7_0,esk5_0,esk8_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_44]),c_0_26]),c_0_46])]),c_0_67])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk10_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_77,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_78,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_79,plain,(
    ! [X21,X22] :
      ( ( ~ v3_pre_topc(X22,X21)
        | r2_hidden(X22,u1_pre_topc(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_pre_topc(X21) )
      & ( ~ r2_hidden(X22,u1_pre_topc(X21))
        | v3_pre_topc(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_80,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_81,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_42])).

cnf(c_0_82,negated_conjecture,
    ( r1_tmap_1(esk7_0,esk5_0,esk8_0,X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X2,esk5_0,k2_tmap_1(esk7_0,esk5_0,esk8_0,X2),X1)
    | ~ v1_tsep_1(X2,esk7_0)
    | ~ m1_pre_topc(X2,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_35]),c_0_36]),c_0_37]),c_0_50]),c_0_38]),c_0_51]),c_0_39])]),c_0_40]),c_0_52])).

cnf(c_0_83,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk5_0,k2_tmap_1(esk7_0,esk5_0,esk8_0,esk6_0),esk9_0) ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_76,c_0_65])).

cnf(c_0_85,negated_conjecture,
    ( ~ r1_tmap_1(esk7_0,esk5_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_86,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_87,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_77]),c_0_78])).

cnf(c_0_88,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_89,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_71]),c_0_24])).

cnf(c_0_90,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_30]),c_0_50]),c_0_31])])).

cnf(c_0_91,negated_conjecture,
    ( ~ v1_tsep_1(esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_48]),c_0_84])]),c_0_85]),c_0_86])).

cnf(c_0_92,plain,
    ( v1_tsep_1(X1,X2)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_78])).

cnf(c_0_93,negated_conjecture,
    ( u1_struct_0(esk6_0) = u1_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_48]),c_0_31])])).

fof(c_0_94,plain,(
    ! [X14,X15,X16,X17] :
      ( ( r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | ~ r1_tarski(X15,u1_pre_topc(X14))
        | r2_hidden(k5_setfam_1(u1_struct_0(X14),X15),u1_pre_topc(X14))
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ r2_hidden(X16,u1_pre_topc(X14))
        | ~ r2_hidden(X17,u1_pre_topc(X14))
        | r2_hidden(k9_subset_1(u1_struct_0(X14),X16,X17),u1_pre_topc(X14))
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk2_1(X14),k1_zfmisc_1(u1_struct_0(X14)))
        | m1_subset_1(esk1_1(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk3_1(X14),k1_zfmisc_1(u1_struct_0(X14)))
        | m1_subset_1(esk1_1(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( r2_hidden(esk2_1(X14),u1_pre_topc(X14))
        | m1_subset_1(esk1_1(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( r2_hidden(esk3_1(X14),u1_pre_topc(X14))
        | m1_subset_1(esk1_1(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X14),esk2_1(X14),esk3_1(X14)),u1_pre_topc(X14))
        | m1_subset_1(esk1_1(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk2_1(X14),k1_zfmisc_1(u1_struct_0(X14)))
        | r1_tarski(esk1_1(X14),u1_pre_topc(X14))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk3_1(X14),k1_zfmisc_1(u1_struct_0(X14)))
        | r1_tarski(esk1_1(X14),u1_pre_topc(X14))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( r2_hidden(esk2_1(X14),u1_pre_topc(X14))
        | r1_tarski(esk1_1(X14),u1_pre_topc(X14))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( r2_hidden(esk3_1(X14),u1_pre_topc(X14))
        | r1_tarski(esk1_1(X14),u1_pre_topc(X14))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X14),esk2_1(X14),esk3_1(X14)),u1_pre_topc(X14))
        | r1_tarski(esk1_1(X14),u1_pre_topc(X14))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk2_1(X14),k1_zfmisc_1(u1_struct_0(X14)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X14),esk1_1(X14)),u1_pre_topc(X14))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk3_1(X14),k1_zfmisc_1(u1_struct_0(X14)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X14),esk1_1(X14)),u1_pre_topc(X14))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( r2_hidden(esk2_1(X14),u1_pre_topc(X14))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X14),esk1_1(X14)),u1_pre_topc(X14))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( r2_hidden(esk3_1(X14),u1_pre_topc(X14))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X14),esk1_1(X14)),u1_pre_topc(X14))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X14),esk2_1(X14),esk3_1(X14)),u1_pre_topc(X14))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X14),esk1_1(X14)),u1_pre_topc(X14))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_95,negated_conjecture,
    ( ~ r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93]),c_0_48]),c_0_50]),c_0_51])])).

cnf(c_0_96,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_50]),c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.033 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t88_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=X4=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))=>r1_tmap_1(X4,X2,X5,X6)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 0.19/0.40  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.19/0.40  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.40  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.19/0.40  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.19/0.40  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.19/0.40  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.19/0.40  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.19/0.40  fof(t67_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:(((~(v2_struct_0(X4))&v1_tsep_1(X4,X2))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>(X5=X6=>(r1_tmap_1(X2,X1,X3,X5)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 0.19/0.40  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.19/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.40  fof(t35_borsuk_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>r1_tarski(u1_struct_0(X2),u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 0.19/0.40  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.19/0.40  fof(t16_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 0.19/0.40  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.19/0.40  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.19/0.40  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.19/0.40  fof(c_0_17, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=X4=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))=>r1_tmap_1(X4,X2,X5,X6))))))))))), inference(assume_negation,[status(cth)],[t88_tmap_1])).
% 0.19/0.40  fof(c_0_18, plain, ![X30, X31]:((~m1_pre_topc(X30,X31)|m1_pre_topc(X30,g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))|~l1_pre_topc(X31)|~l1_pre_topc(X30))&(~m1_pre_topc(X30,g1_pre_topc(u1_struct_0(X31),u1_pre_topc(X31)))|m1_pre_topc(X30,X31)|~l1_pre_topc(X31)|~l1_pre_topc(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.19/0.40  fof(c_0_19, plain, ![X23, X24]:(~l1_pre_topc(X23)|(~m1_pre_topc(X24,X23)|l1_pre_topc(X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.40  fof(c_0_20, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&((~v2_struct_0(esk6_0)&m1_pre_topc(esk6_0,esk4_0))&((~v2_struct_0(esk7_0)&m1_pre_topc(esk7_0,esk4_0))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0)))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0)))))&(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))=esk7_0&(m1_subset_1(esk9_0,u1_struct_0(esk7_0))&(m1_subset_1(esk10_0,u1_struct_0(esk6_0))&((esk9_0=esk10_0&r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk10_0))&~r1_tmap_1(esk7_0,esk5_0,esk8_0,esk9_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.19/0.40  fof(c_0_21, plain, ![X36, X37, X38, X39, X40]:(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|(~m1_pre_topc(X38,X36)|(~m1_pre_topc(X39,X36)|(~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X37))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X37))))|(~m1_pre_topc(X39,X38)|k3_tmap_1(X36,X37,X38,X39,X40)=k2_partfun1(u1_struct_0(X38),u1_struct_0(X37),X40,u1_struct_0(X39)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.19/0.40  fof(c_0_22, plain, ![X55, X56, X57]:(~v2_pre_topc(X55)|~l1_pre_topc(X55)|(~m1_pre_topc(X56,X55)|(~m1_pre_topc(X57,X56)|m1_pre_topc(X57,X55)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.19/0.40  cnf(c_0_23, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_24, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_25, negated_conjecture, (m1_pre_topc(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_27, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.40  cnf(c_0_28, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.40  cnf(c_0_29, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.40  cnf(c_0_30, negated_conjecture, (g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))=esk7_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_31, negated_conjecture, (l1_pre_topc(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.19/0.40  fof(c_0_32, plain, ![X46]:(~l1_pre_topc(X46)|m1_pre_topc(X46,X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.19/0.40  fof(c_0_33, plain, ![X12, X13]:(~v2_pre_topc(X12)|~l1_pre_topc(X12)|(~m1_pre_topc(X13,X12)|v2_pre_topc(X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.19/0.40  cnf(c_0_34, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(csr,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.40  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_38, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_39, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_40, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_41, negated_conjecture, (m1_pre_topc(X1,esk7_0)|~m1_pre_topc(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.19/0.40  cnf(c_0_42, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.40  fof(c_0_43, plain, ![X32, X33, X34, X35]:(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|(~v1_funct_1(X34)|~v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X33))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))|(~m1_pre_topc(X35,X32)|k2_tmap_1(X32,X33,X34,X35)=k2_partfun1(u1_struct_0(X32),u1_struct_0(X33),X34,u1_struct_0(X35)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.19/0.40  cnf(c_0_44, negated_conjecture, (m1_pre_topc(esk7_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_45, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.40  cnf(c_0_46, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_47, negated_conjecture, (k3_tmap_1(X1,esk5_0,esk7_0,X2,esk8_0)=k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk7_0)|~m1_pre_topc(esk7_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])]), c_0_40])).
% 0.19/0.40  cnf(c_0_48, negated_conjecture, (m1_pre_topc(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_31])])).
% 0.19/0.40  cnf(c_0_49, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.40  cnf(c_0_50, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_44]), c_0_26])])).
% 0.19/0.40  cnf(c_0_51, negated_conjecture, (v2_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_44]), c_0_26]), c_0_46])])).
% 0.19/0.40  cnf(c_0_52, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_53, negated_conjecture, (k3_tmap_1(X1,esk5_0,esk7_0,esk6_0,esk8_0)=k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(esk6_0))|v2_struct_0(X1)|~m1_pre_topc(esk7_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.40  cnf(c_0_54, negated_conjecture, (k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(X1))=k2_tmap_1(esk7_0,esk5_0,esk8_0,X1)|~m1_pre_topc(X1,esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_50]), c_0_39]), c_0_51])]), c_0_40]), c_0_52])).
% 0.19/0.40  cnf(c_0_55, negated_conjecture, (k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(esk6_0))=k3_tmap_1(esk7_0,esk5_0,esk7_0,esk6_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_42]), c_0_50]), c_0_51])]), c_0_52])).
% 0.19/0.40  fof(c_0_56, plain, ![X49, X50, X51, X52, X53, X54]:((~r1_tmap_1(X50,X49,X51,X53)|r1_tmap_1(X52,X49,k2_tmap_1(X50,X49,X51,X52),X54)|X53!=X54|~m1_subset_1(X54,u1_struct_0(X52))|~m1_subset_1(X53,u1_struct_0(X50))|(v2_struct_0(X52)|~v1_tsep_1(X52,X50)|~m1_pre_topc(X52,X50))|(~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X50),u1_struct_0(X49))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X49)))))|(v2_struct_0(X50)|~v2_pre_topc(X50)|~l1_pre_topc(X50))|(v2_struct_0(X49)|~v2_pre_topc(X49)|~l1_pre_topc(X49)))&(~r1_tmap_1(X52,X49,k2_tmap_1(X50,X49,X51,X52),X54)|r1_tmap_1(X50,X49,X51,X53)|X53!=X54|~m1_subset_1(X54,u1_struct_0(X52))|~m1_subset_1(X53,u1_struct_0(X50))|(v2_struct_0(X52)|~v1_tsep_1(X52,X50)|~m1_pre_topc(X52,X50))|(~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X50),u1_struct_0(X49))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X49)))))|(v2_struct_0(X50)|~v2_pre_topc(X50)|~l1_pre_topc(X50))|(v2_struct_0(X49)|~v2_pre_topc(X49)|~l1_pre_topc(X49)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_tmap_1])])])])])).
% 0.19/0.40  fof(c_0_57, plain, ![X25, X26, X27]:(v2_struct_0(X25)|~l1_pre_topc(X25)|(v2_struct_0(X26)|~m1_pre_topc(X26,X25)|(~m1_subset_1(X27,u1_struct_0(X26))|m1_subset_1(X27,u1_struct_0(X25))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.19/0.40  cnf(c_0_58, negated_conjecture, (k3_tmap_1(esk7_0,esk5_0,esk7_0,esk6_0,esk8_0)=k2_tmap_1(esk7_0,esk5_0,esk8_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_48])])).
% 0.19/0.40  fof(c_0_59, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.40  fof(c_0_60, plain, ![X47, X48]:(~l1_pre_topc(X47)|(~m1_pre_topc(X48,X47)|r1_tarski(u1_struct_0(X48),u1_struct_0(X47)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).
% 0.19/0.40  fof(c_0_61, plain, ![X28, X29]:(~l1_pre_topc(X28)|(~m1_pre_topc(X29,g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28)))|m1_pre_topc(X29,X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.19/0.40  cnf(c_0_62, plain, (r1_tmap_1(X3,X2,X4,X6)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|X6!=X5|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X6,u1_struct_0(X3))|~v1_tsep_1(X1,X3)|~m1_pre_topc(X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.40  cnf(c_0_63, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.40  cnf(c_0_64, negated_conjecture, (r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk10_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_65, negated_conjecture, (esk9_0=esk10_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_66, negated_conjecture, (k3_tmap_1(X1,esk5_0,esk7_0,esk6_0,esk8_0)=k2_tmap_1(esk7_0,esk5_0,esk8_0,esk6_0)|v2_struct_0(X1)|~m1_pre_topc(esk7_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_55]), c_0_58])).
% 0.19/0.40  cnf(c_0_67, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  fof(c_0_68, plain, ![X41, X42, X43]:((~v1_tsep_1(X42,X41)|~m1_pre_topc(X42,X41)|v3_pre_topc(X43,X41)|X43!=u1_struct_0(X42)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))|~m1_pre_topc(X42,X41)|(~v2_pre_topc(X41)|~l1_pre_topc(X41)))&((v1_tsep_1(X42,X41)|~v3_pre_topc(X43,X41)|X43!=u1_struct_0(X42)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))|~m1_pre_topc(X42,X41)|(~v2_pre_topc(X41)|~l1_pre_topc(X41)))&(m1_pre_topc(X42,X41)|~v3_pre_topc(X43,X41)|X43!=u1_struct_0(X42)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))|~m1_pre_topc(X42,X41)|(~v2_pre_topc(X41)|~l1_pre_topc(X41))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).
% 0.19/0.40  fof(c_0_69, plain, ![X44, X45]:(~l1_pre_topc(X44)|(~m1_pre_topc(X45,X44)|m1_subset_1(u1_struct_0(X45),k1_zfmisc_1(u1_struct_0(X44))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.19/0.40  cnf(c_0_70, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.40  cnf(c_0_71, plain, (r1_tarski(u1_struct_0(X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.40  cnf(c_0_72, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.40  cnf(c_0_73, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X5)|~r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)|~v1_tsep_1(X5,X1)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~m1_pre_topc(X5,X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~v2_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,u1_struct_0(X5))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_62]), c_0_63])).
% 0.19/0.40  cnf(c_0_74, negated_conjecture, (r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk9_0)), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.40  cnf(c_0_75, negated_conjecture, (k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0)=k2_tmap_1(esk7_0,esk5_0,esk8_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_44]), c_0_26]), c_0_46])]), c_0_67])).
% 0.19/0.40  cnf(c_0_76, negated_conjecture, (m1_subset_1(esk10_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_77, plain, (v1_tsep_1(X1,X2)|~v3_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.40  cnf(c_0_78, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.40  fof(c_0_79, plain, ![X21, X22]:((~v3_pre_topc(X22,X21)|r2_hidden(X22,u1_pre_topc(X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~l1_pre_topc(X21))&(~r2_hidden(X22,u1_pre_topc(X21))|v3_pre_topc(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~l1_pre_topc(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.19/0.40  cnf(c_0_80, plain, (u1_struct_0(X1)=u1_struct_0(X2)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.40  cnf(c_0_81, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X1)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_72, c_0_42])).
% 0.19/0.40  cnf(c_0_82, negated_conjecture, (r1_tmap_1(esk7_0,esk5_0,esk8_0,X1)|v2_struct_0(X2)|~r1_tmap_1(X2,esk5_0,k2_tmap_1(esk7_0,esk5_0,esk8_0,X2),X1)|~v1_tsep_1(X2,esk7_0)|~m1_pre_topc(X2,esk7_0)|~m1_subset_1(X1,u1_struct_0(X2))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_35]), c_0_36]), c_0_37]), c_0_50]), c_0_38]), c_0_51]), c_0_39])]), c_0_40]), c_0_52])).
% 0.19/0.40  cnf(c_0_83, negated_conjecture, (r1_tmap_1(esk6_0,esk5_0,k2_tmap_1(esk7_0,esk5_0,esk8_0,esk6_0),esk9_0)), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 0.19/0.40  cnf(c_0_84, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk6_0))), inference(rw,[status(thm)],[c_0_76, c_0_65])).
% 0.19/0.40  cnf(c_0_85, negated_conjecture, (~r1_tmap_1(esk7_0,esk5_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_86, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_87, plain, (v1_tsep_1(X1,X2)|~v3_pre_topc(u1_struct_0(X1),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_77]), c_0_78])).
% 0.19/0.40  cnf(c_0_88, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.19/0.40  cnf(c_0_89, plain, (u1_struct_0(X1)=u1_struct_0(X2)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_71]), c_0_24])).
% 0.19/0.40  cnf(c_0_90, negated_conjecture, (m1_pre_topc(esk7_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_30]), c_0_50]), c_0_31])])).
% 0.19/0.40  cnf(c_0_91, negated_conjecture, (~v1_tsep_1(esk6_0,esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_48]), c_0_84])]), c_0_85]), c_0_86])).
% 0.19/0.40  cnf(c_0_92, plain, (v1_tsep_1(X1,X2)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_78])).
% 0.19/0.40  cnf(c_0_93, negated_conjecture, (u1_struct_0(esk6_0)=u1_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_48]), c_0_31])])).
% 0.19/0.40  fof(c_0_94, plain, ![X14, X15, X16, X17]:((((r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))|~v2_pre_topc(X14)|~l1_pre_topc(X14))&(~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))|(~r1_tarski(X15,u1_pre_topc(X14))|r2_hidden(k5_setfam_1(u1_struct_0(X14),X15),u1_pre_topc(X14)))|~v2_pre_topc(X14)|~l1_pre_topc(X14)))&(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X14)))|(~r2_hidden(X16,u1_pre_topc(X14))|~r2_hidden(X17,u1_pre_topc(X14))|r2_hidden(k9_subset_1(u1_struct_0(X14),X16,X17),u1_pre_topc(X14))))|~v2_pre_topc(X14)|~l1_pre_topc(X14)))&(((m1_subset_1(esk2_1(X14),k1_zfmisc_1(u1_struct_0(X14)))|(m1_subset_1(esk1_1(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14))&((m1_subset_1(esk3_1(X14),k1_zfmisc_1(u1_struct_0(X14)))|(m1_subset_1(esk1_1(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14))&(((r2_hidden(esk2_1(X14),u1_pre_topc(X14))|(m1_subset_1(esk1_1(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14))&(r2_hidden(esk3_1(X14),u1_pre_topc(X14))|(m1_subset_1(esk1_1(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14)))&(~r2_hidden(k9_subset_1(u1_struct_0(X14),esk2_1(X14),esk3_1(X14)),u1_pre_topc(X14))|(m1_subset_1(esk1_1(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14)))))&(((m1_subset_1(esk2_1(X14),k1_zfmisc_1(u1_struct_0(X14)))|(r1_tarski(esk1_1(X14),u1_pre_topc(X14))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14))&((m1_subset_1(esk3_1(X14),k1_zfmisc_1(u1_struct_0(X14)))|(r1_tarski(esk1_1(X14),u1_pre_topc(X14))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14))&(((r2_hidden(esk2_1(X14),u1_pre_topc(X14))|(r1_tarski(esk1_1(X14),u1_pre_topc(X14))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14))&(r2_hidden(esk3_1(X14),u1_pre_topc(X14))|(r1_tarski(esk1_1(X14),u1_pre_topc(X14))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14)))&(~r2_hidden(k9_subset_1(u1_struct_0(X14),esk2_1(X14),esk3_1(X14)),u1_pre_topc(X14))|(r1_tarski(esk1_1(X14),u1_pre_topc(X14))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14)))))&((m1_subset_1(esk2_1(X14),k1_zfmisc_1(u1_struct_0(X14)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X14),esk1_1(X14)),u1_pre_topc(X14))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14))&((m1_subset_1(esk3_1(X14),k1_zfmisc_1(u1_struct_0(X14)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X14),esk1_1(X14)),u1_pre_topc(X14))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14))&(((r2_hidden(esk2_1(X14),u1_pre_topc(X14))|(~r2_hidden(k5_setfam_1(u1_struct_0(X14),esk1_1(X14)),u1_pre_topc(X14))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14))&(r2_hidden(esk3_1(X14),u1_pre_topc(X14))|(~r2_hidden(k5_setfam_1(u1_struct_0(X14),esk1_1(X14)),u1_pre_topc(X14))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14)))&(~r2_hidden(k9_subset_1(u1_struct_0(X14),esk2_1(X14),esk3_1(X14)),u1_pre_topc(X14))|(~r2_hidden(k5_setfam_1(u1_struct_0(X14),esk1_1(X14)),u1_pre_topc(X14))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.19/0.40  cnf(c_0_95, negated_conjecture, (~r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93]), c_0_48]), c_0_50]), c_0_51])])).
% 0.19/0.40  cnf(c_0_96, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.19/0.40  cnf(c_0_97, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_50]), c_0_51])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 98
% 0.19/0.40  # Proof object clause steps            : 63
% 0.19/0.40  # Proof object formula steps           : 35
% 0.19/0.40  # Proof object conjectures             : 42
% 0.19/0.40  # Proof object clause conjectures      : 39
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 34
% 0.19/0.40  # Proof object initial formulas used   : 17
% 0.19/0.40  # Proof object generating inferences   : 21
% 0.19/0.40  # Proof object simplifying inferences  : 77
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 19
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 61
% 0.19/0.40  # Removed in clause preprocessing      : 2
% 0.19/0.40  # Initial clauses in saturation        : 59
% 0.19/0.40  # Processed clauses                    : 327
% 0.19/0.40  # ...of these trivial                  : 11
% 0.19/0.40  # ...subsumed                          : 66
% 0.19/0.40  # ...remaining for further processing  : 250
% 0.19/0.40  # Other redundant clauses eliminated   : 6
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 0
% 0.19/0.40  # Backward-rewritten                   : 26
% 0.19/0.40  # Generated clauses                    : 457
% 0.19/0.40  # ...of the previous two non-trivial   : 313
% 0.19/0.40  # Contextual simplify-reflections      : 13
% 0.19/0.40  # Paramodulations                      : 451
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 6
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 161
% 0.19/0.40  #    Positive orientable unit clauses  : 37
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 7
% 0.19/0.40  #    Non-unit-clauses                  : 117
% 0.19/0.40  # Current number of unprocessed clauses: 91
% 0.19/0.40  # ...number of literals in the above   : 598
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 84
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 9330
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 989
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 78
% 0.19/0.40  # Unit Clause-clause subsumption calls : 533
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 39
% 0.19/0.40  # BW rewrite match successes           : 11
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 19410
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.064 s
% 0.19/0.40  # System time              : 0.002 s
% 0.19/0.40  # Total time               : 0.066 s
% 0.19/0.40  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
