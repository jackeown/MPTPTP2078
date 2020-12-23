%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:56 EST 2020

% Result     : Theorem 0.35s
% Output     : CNFRefutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  152 (9203 expanded)
%              Number of clauses        :  109 (3460 expanded)
%              Number of leaves         :   21 (2275 expanded)
%              Depth                    :   21
%              Number of atoms          :  777 (84224 expanded)
%              Number of equality atoms :   68 (7781 expanded)
%              Maximal formula depth    :   27 (   5 average)
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

fof(t11_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(t4_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
              <=> m1_pre_topc(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

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

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

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

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

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

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(c_0_21,negated_conjecture,(
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

fof(c_0_22,plain,(
    ! [X36,X37] :
      ( ( ~ m1_pre_topc(X36,X37)
        | m1_pre_topc(X36,g1_pre_topc(u1_struct_0(X37),u1_pre_topc(X37)))
        | ~ l1_pre_topc(X37)
        | ~ l1_pre_topc(X36) )
      & ( ~ m1_pre_topc(X36,g1_pre_topc(u1_struct_0(X37),u1_pre_topc(X37)))
        | m1_pre_topc(X36,X37)
        | ~ l1_pre_topc(X37)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

fof(c_0_23,plain,(
    ! [X24,X25] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_pre_topc(X25,X24)
      | l1_pre_topc(X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_24,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

fof(c_0_25,plain,(
    ! [X47,X48] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X48),u1_pre_topc(X48)))
        | ~ m1_pre_topc(X48,X47)
        | ~ l1_pre_topc(X47) )
      & ( m1_pre_topc(g1_pre_topc(u1_struct_0(X48),u1_pre_topc(X48)),X47)
        | ~ m1_pre_topc(X48,X47)
        | ~ l1_pre_topc(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).

cnf(c_0_26,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_32,plain,(
    ! [X54] :
      ( ~ l1_pre_topc(X54)
      | m1_pre_topc(X54,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

fof(c_0_33,plain,(
    ! [X55,X56,X57] :
      ( ( ~ r1_tarski(u1_struct_0(X56),u1_struct_0(X57))
        | m1_pre_topc(X56,X57)
        | ~ m1_pre_topc(X57,X55)
        | ~ m1_pre_topc(X56,X55)
        | ~ v2_pre_topc(X55)
        | ~ l1_pre_topc(X55) )
      & ( ~ m1_pre_topc(X56,X57)
        | r1_tarski(u1_struct_0(X56),u1_struct_0(X57))
        | ~ m1_pre_topc(X57,X55)
        | ~ m1_pre_topc(X56,X55)
        | ~ v2_pre_topc(X55)
        | ~ l1_pre_topc(X55) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

fof(c_0_34,plain,(
    ! [X64,X65,X66] :
      ( ~ v2_pre_topc(X64)
      | ~ l1_pre_topc(X64)
      | ~ m1_pre_topc(X65,X64)
      | ~ m1_pre_topc(X66,X65)
      | m1_pre_topc(X66,X64) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

cnf(c_0_35,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_37,negated_conjecture,
    ( m1_pre_topc(esk7_0,X1)
    | ~ m1_pre_topc(esk6_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_39,plain,(
    ! [X13,X14] :
      ( ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(X14,X13)
      | v2_pre_topc(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_40,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_41,plain,(
    ! [X10,X11] :
      ( ( ~ m1_subset_1(X10,k1_zfmisc_1(X11))
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | m1_subset_1(X10,k1_zfmisc_1(X11)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_42,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( m1_pre_topc(X1,esk7_0)
    | ~ m1_pre_topc(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_31]),c_0_36])])).

cnf(c_0_45,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_36])])).

cnf(c_0_46,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_48,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_49,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_29])])).

cnf(c_0_54,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_47]),c_0_29])])).

cnf(c_0_55,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_38]),c_0_36])])).

fof(c_0_56,plain,(
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

cnf(c_0_57,plain,
    ( X1 = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk7_0))
    | ~ m1_pre_topc(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54])])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk6_0))
    | ~ m1_pre_topc(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_55]),c_0_53]),c_0_54])])).

cnf(c_0_61,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_65,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_66,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_67,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_68,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_69,negated_conjecture,
    ( u1_struct_0(esk7_0) = u1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk7_0)
    | ~ m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_pre_topc(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

fof(c_0_71,plain,(
    ! [X42,X43,X44,X45,X46] :
      ( v2_struct_0(X42)
      | ~ v2_pre_topc(X42)
      | ~ l1_pre_topc(X42)
      | v2_struct_0(X43)
      | ~ v2_pre_topc(X43)
      | ~ l1_pre_topc(X43)
      | ~ m1_pre_topc(X44,X42)
      | ~ m1_pre_topc(X45,X42)
      | ~ v1_funct_1(X46)
      | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X43))
      | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X43))))
      | ~ m1_pre_topc(X45,X44)
      | k3_tmap_1(X42,X43,X44,X45,X46) = k2_partfun1(u1_struct_0(X44),u1_struct_0(X43),X46,u1_struct_0(X45)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_72,plain,(
    ! [X58,X59,X60,X61,X62,X63] :
      ( ( ~ r1_tmap_1(X59,X58,X60,X62)
        | r1_tmap_1(X61,X58,k2_tmap_1(X59,X58,X60,X61),X63)
        | X62 != X63
        | ~ m1_subset_1(X63,u1_struct_0(X61))
        | ~ m1_subset_1(X62,u1_struct_0(X59))
        | v2_struct_0(X61)
        | ~ v1_tsep_1(X61,X59)
        | ~ m1_pre_topc(X61,X59)
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,u1_struct_0(X59),u1_struct_0(X58))
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X59),u1_struct_0(X58))))
        | v2_struct_0(X59)
        | ~ v2_pre_topc(X59)
        | ~ l1_pre_topc(X59)
        | v2_struct_0(X58)
        | ~ v2_pre_topc(X58)
        | ~ l1_pre_topc(X58) )
      & ( ~ r1_tmap_1(X61,X58,k2_tmap_1(X59,X58,X60,X61),X63)
        | r1_tmap_1(X59,X58,X60,X62)
        | X62 != X63
        | ~ m1_subset_1(X63,u1_struct_0(X61))
        | ~ m1_subset_1(X62,u1_struct_0(X59))
        | v2_struct_0(X61)
        | ~ v1_tsep_1(X61,X59)
        | ~ m1_pre_topc(X61,X59)
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,u1_struct_0(X59),u1_struct_0(X58))
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X59),u1_struct_0(X58))))
        | v2_struct_0(X59)
        | ~ v2_pre_topc(X59)
        | ~ l1_pre_topc(X59)
        | v2_struct_0(X58)
        | ~ v2_pre_topc(X58)
        | ~ l1_pre_topc(X58) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_tmap_1])])])])])).

fof(c_0_73,plain,(
    ! [X31,X32,X33] :
      ( v2_struct_0(X31)
      | ~ l1_pre_topc(X31)
      | v2_struct_0(X32)
      | ~ m1_pre_topc(X32,X31)
      | ~ m1_subset_1(X33,u1_struct_0(X32))
      | m1_subset_1(X33,u1_struct_0(X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_74,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(X1)) = k2_tmap_1(esk7_0,esk5_0,esk8_0,X1)
    | ~ m1_pre_topc(X1,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64]),c_0_65]),c_0_53]),c_0_66]),c_0_54])]),c_0_67]),c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( u1_struct_0(esk6_0) = u1_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_55]),c_0_45])])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_77,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_71])).

fof(c_0_78,plain,(
    ! [X26] :
      ( ~ l1_pre_topc(X26)
      | m1_subset_1(u1_pre_topc(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_79,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_80,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_28]),c_0_48]),c_0_29])])).

cnf(c_0_82,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_83,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(esk7_0)) = k2_tmap_1(esk7_0,esk5_0,esk8_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_55])])).

cnf(c_0_84,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_76])).

cnf(c_0_86,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[c_0_77,c_0_43])).

fof(c_0_87,plain,(
    ! [X27,X28,X29,X30] :
      ( ( X27 = X29
        | g1_pre_topc(X27,X28) != g1_pre_topc(X29,X30)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X27))) )
      & ( X28 = X30
        | g1_pre_topc(X27,X28) != g1_pre_topc(X29,X30)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

cnf(c_0_88,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

fof(c_0_89,plain,(
    ! [X12] :
      ( ~ l1_pre_topc(X12)
      | ~ v1_pre_topc(X12)
      | X12 = g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_90,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_91,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | ~ r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)
    | ~ v1_tsep_1(X5,X1)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_pre_topc(X5,X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,u1_struct_0(X5)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_79]),c_0_80])).

cnf(c_0_92,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(esk6_0,X1,X2,X3)
    | v2_struct_0(X1)
    | ~ v1_funct_2(X2,u1_struct_0(esk7_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_pre_topc(X3,esk6_0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(X1)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_75]),c_0_81]),c_0_36])]),c_0_82])).

cnf(c_0_93,negated_conjecture,
    ( k2_tmap_1(esk7_0,esk5_0,esk8_0,esk6_0) = k2_tmap_1(esk7_0,esk5_0,esk8_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_83]),c_0_63]),c_0_64]),c_0_52]),c_0_65]),c_0_53]),c_0_66]),c_0_54]),c_0_62])]),c_0_67]),c_0_68])).

cnf(c_0_94,plain,
    ( m1_pre_topc(X1,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_95,negated_conjecture,
    ( k3_tmap_1(X1,esk5_0,esk7_0,X2,esk8_0) = k2_tmap_1(esk7_0,esk5_0,esk8_0,X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk7_0)
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_74]),c_0_63]),c_0_64]),c_0_65]),c_0_66]),c_0_62])]),c_0_67])).

cnf(c_0_96,negated_conjecture,
    ( m1_pre_topc(esk6_0,X1)
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_55])).

fof(c_0_97,plain,(
    ! [X49,X50,X51] :
      ( ( ~ v1_tsep_1(X50,X49)
        | ~ m1_pre_topc(X50,X49)
        | v3_pre_topc(X51,X49)
        | X51 != u1_struct_0(X50)
        | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))
        | ~ m1_pre_topc(X50,X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49) )
      & ( v1_tsep_1(X50,X49)
        | ~ v3_pre_topc(X51,X49)
        | X51 != u1_struct_0(X50)
        | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))
        | ~ m1_pre_topc(X50,X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49) )
      & ( m1_pre_topc(X50,X49)
        | ~ v3_pre_topc(X51,X49)
        | X51 != u1_struct_0(X50)
        | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))
        | ~ m1_pre_topc(X50,X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).

fof(c_0_98,plain,(
    ! [X15,X16,X17,X18] :
      ( ( r2_hidden(u1_struct_0(X15),u1_pre_topc(X15))
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ r1_tarski(X16,u1_pre_topc(X15))
        | r2_hidden(k5_setfam_1(u1_struct_0(X15),X16),u1_pre_topc(X15))
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ r2_hidden(X17,u1_pre_topc(X15))
        | ~ r2_hidden(X18,u1_pre_topc(X15))
        | r2_hidden(k9_subset_1(u1_struct_0(X15),X17,X18),u1_pre_topc(X15))
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk2_1(X15),k1_zfmisc_1(u1_struct_0(X15)))
        | m1_subset_1(esk1_1(X15),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ r2_hidden(u1_struct_0(X15),u1_pre_topc(X15))
        | v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk3_1(X15),k1_zfmisc_1(u1_struct_0(X15)))
        | m1_subset_1(esk1_1(X15),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ r2_hidden(u1_struct_0(X15),u1_pre_topc(X15))
        | v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( r2_hidden(esk2_1(X15),u1_pre_topc(X15))
        | m1_subset_1(esk1_1(X15),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ r2_hidden(u1_struct_0(X15),u1_pre_topc(X15))
        | v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( r2_hidden(esk3_1(X15),u1_pre_topc(X15))
        | m1_subset_1(esk1_1(X15),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ r2_hidden(u1_struct_0(X15),u1_pre_topc(X15))
        | v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X15),esk2_1(X15),esk3_1(X15)),u1_pre_topc(X15))
        | m1_subset_1(esk1_1(X15),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ r2_hidden(u1_struct_0(X15),u1_pre_topc(X15))
        | v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk2_1(X15),k1_zfmisc_1(u1_struct_0(X15)))
        | r1_tarski(esk1_1(X15),u1_pre_topc(X15))
        | ~ r2_hidden(u1_struct_0(X15),u1_pre_topc(X15))
        | v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk3_1(X15),k1_zfmisc_1(u1_struct_0(X15)))
        | r1_tarski(esk1_1(X15),u1_pre_topc(X15))
        | ~ r2_hidden(u1_struct_0(X15),u1_pre_topc(X15))
        | v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( r2_hidden(esk2_1(X15),u1_pre_topc(X15))
        | r1_tarski(esk1_1(X15),u1_pre_topc(X15))
        | ~ r2_hidden(u1_struct_0(X15),u1_pre_topc(X15))
        | v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( r2_hidden(esk3_1(X15),u1_pre_topc(X15))
        | r1_tarski(esk1_1(X15),u1_pre_topc(X15))
        | ~ r2_hidden(u1_struct_0(X15),u1_pre_topc(X15))
        | v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X15),esk2_1(X15),esk3_1(X15)),u1_pre_topc(X15))
        | r1_tarski(esk1_1(X15),u1_pre_topc(X15))
        | ~ r2_hidden(u1_struct_0(X15),u1_pre_topc(X15))
        | v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk2_1(X15),k1_zfmisc_1(u1_struct_0(X15)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X15),esk1_1(X15)),u1_pre_topc(X15))
        | ~ r2_hidden(u1_struct_0(X15),u1_pre_topc(X15))
        | v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk3_1(X15),k1_zfmisc_1(u1_struct_0(X15)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X15),esk1_1(X15)),u1_pre_topc(X15))
        | ~ r2_hidden(u1_struct_0(X15),u1_pre_topc(X15))
        | v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( r2_hidden(esk2_1(X15),u1_pre_topc(X15))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X15),esk1_1(X15)),u1_pre_topc(X15))
        | ~ r2_hidden(u1_struct_0(X15),u1_pre_topc(X15))
        | v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( r2_hidden(esk3_1(X15),u1_pre_topc(X15))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X15),esk1_1(X15)),u1_pre_topc(X15))
        | ~ r2_hidden(u1_struct_0(X15),u1_pre_topc(X15))
        | v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X15),esk2_1(X15),esk3_1(X15)),u1_pre_topc(X15))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X15),esk1_1(X15)),u1_pre_topc(X15))
        | ~ r2_hidden(u1_struct_0(X15),u1_pre_topc(X15))
        | v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_99,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk6_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_75]),c_0_36])])).

cnf(c_0_101,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk6_0)) = esk7_0 ),
    inference(rw,[status(thm)],[c_0_31,c_0_75])).

cnf(c_0_102,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_103,negated_conjecture,
    ( v1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_28]),c_0_31]),c_0_29])])).

fof(c_0_104,plain,(
    ! [X34,X35] :
      ( ~ l1_pre_topc(X34)
      | ~ m1_pre_topc(X35,g1_pre_topc(u1_struct_0(X34),u1_pre_topc(X34)))
      | m1_pre_topc(X35,X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

cnf(c_0_105,negated_conjecture,
    ( r1_tmap_1(esk6_0,X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(esk6_0,X1,X2,X4),X3)
    | ~ v1_tsep_1(X4,esk6_0)
    | ~ v1_funct_2(X2,u1_struct_0(esk7_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_pre_topc(X4,esk6_0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_75]),c_0_81]),c_0_36])]),c_0_82])).

cnf(c_0_106,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(X1)) = k2_tmap_1(esk6_0,esk5_0,esk8_0,X1)
    | ~ m1_pre_topc(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_62]),c_0_63]),c_0_64]),c_0_65]),c_0_66])]),c_0_67])).

cnf(c_0_107,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(esk7_0)) = k2_tmap_1(esk7_0,esk5_0,esk8_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_83,c_0_93])).

cnf(c_0_108,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_55]),c_0_53]),c_0_54])])).

cnf(c_0_109,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_110,negated_conjecture,
    ( esk9_0 = esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_111,negated_conjecture,
    ( k3_tmap_1(X1,esk5_0,esk7_0,esk6_0,esk8_0) = k2_tmap_1(esk7_0,esk5_0,esk8_0,esk7_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_93]),c_0_52]),c_0_53]),c_0_54])])).

cnf(c_0_112,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_113,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_114,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_85])).

cnf(c_0_115,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_116,negated_conjecture,
    ( u1_pre_topc(esk6_0) = X1
    | g1_pre_topc(X2,X1) != esk7_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_101])).

cnf(c_0_117,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_54])])).

cnf(c_0_118,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_119,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk5_0,esk8_0,X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X2,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk8_0,X2),X1)
    | ~ v1_tsep_1(X2,esk6_0)
    | ~ m1_pre_topc(X2,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_62]),c_0_63]),c_0_64]),c_0_65]),c_0_66])]),c_0_67])).

cnf(c_0_120,negated_conjecture,
    ( k2_tmap_1(esk6_0,esk5_0,esk8_0,esk6_0) = k2_tmap_1(esk7_0,esk5_0,esk8_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_75]),c_0_107]),c_0_108])])).

cnf(c_0_121,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk9_0) ),
    inference(rw,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_122,negated_conjecture,
    ( k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0) = k2_tmap_1(esk7_0,esk5_0,esk8_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_47]),c_0_48]),c_0_29])]),c_0_112])).

cnf(c_0_123,plain,
    ( v1_tsep_1(X1,X2)
    | u1_struct_0(X2) != u1_struct_0(X1)
    | ~ v3_pre_topc(u1_struct_0(X2),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

fof(c_0_124,plain,(
    ! [X22,X23] :
      ( ( ~ v3_pre_topc(X23,X22)
        | r2_hidden(X23,u1_pre_topc(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) )
      & ( ~ r2_hidden(X23,u1_pre_topc(X22))
        | v3_pre_topc(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_125,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_75]),c_0_81]),c_0_36])])).

cnf(c_0_126,negated_conjecture,
    ( u1_pre_topc(esk6_0) = u1_pre_topc(esk7_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_127,plain,
    ( r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X6)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,X2,X3,X4)
    | X4 != X6
    | ~ m1_subset_1(X6,u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_tsep_1(X5,X1)
    | ~ m1_pre_topc(X5,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_128,negated_conjecture,
    ( m1_pre_topc(X1,esk6_0)
    | ~ m1_pre_topc(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_31]),c_0_36])])).

cnf(c_0_129,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk5_0,esk8_0,X1)
    | ~ r1_tmap_1(esk6_0,esk5_0,k2_tmap_1(esk7_0,esk5_0,esk8_0,esk7_0),X1)
    | ~ v1_tsep_1(esk6_0,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_108]),c_0_75])]),c_0_82])).

cnf(c_0_130,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk5_0,k2_tmap_1(esk7_0,esk5_0,esk8_0,esk7_0),esk9_0) ),
    inference(rw,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_131,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_132,negated_conjecture,
    ( v1_tsep_1(X1,esk6_0)
    | u1_struct_0(esk7_0) != u1_struct_0(X1)
    | ~ v3_pre_topc(u1_struct_0(esk7_0),esk6_0)
    | ~ m1_pre_topc(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_75]),c_0_81]),c_0_36])])).

cnf(c_0_133,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_124])).

cnf(c_0_134,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_135,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X3,X2,X4,X5)
    | ~ v1_tsep_1(X1,X3)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X4)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_127]),c_0_80])).

cnf(c_0_136,negated_conjecture,
    ( k2_tmap_1(esk6_0,esk5_0,esk8_0,X1) = k2_tmap_1(esk7_0,esk5_0,esk8_0,X1)
    | ~ m1_pre_topc(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_106]),c_0_63]),c_0_64]),c_0_65]),c_0_53]),c_0_66]),c_0_54]),c_0_62])]),c_0_67]),c_0_68]),c_0_128])).

cnf(c_0_137,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk5_0,esk8_0,esk9_0)
    | ~ v1_tsep_1(esk6_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_131])])).

cnf(c_0_138,negated_conjecture,
    ( v1_tsep_1(X1,esk6_0)
    | u1_struct_0(esk7_0) != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_126]),c_0_134]),c_0_36]),c_0_75]),c_0_114])])).

cnf(c_0_139,negated_conjecture,
    ( r1_tmap_1(X1,esk5_0,k2_tmap_1(esk7_0,esk5_0,esk8_0,X1),X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk6_0,esk5_0,esk8_0,X2)
    | ~ v1_tsep_1(X1,esk6_0)
    | ~ m1_pre_topc(X1,esk6_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_75]),c_0_63]),c_0_64]),c_0_65]),c_0_81]),c_0_66]),c_0_36]),c_0_75]),c_0_62])]),c_0_82]),c_0_67]),c_0_44])).

cnf(c_0_140,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk5_0,esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_75]),c_0_108])])).

cnf(c_0_141,negated_conjecture,
    ( r1_tmap_1(X1,esk5_0,k2_tmap_1(esk7_0,esk5_0,esk8_0,X1),esk9_0)
    | v2_struct_0(X1)
    | ~ v1_tsep_1(X1,esk6_0)
    | ~ m1_pre_topc(X1,esk6_0)
    | ~ m1_subset_1(esk9_0,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_139,c_0_140])).

cnf(c_0_142,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ m1_pre_topc(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_58])).

cnf(c_0_143,negated_conjecture,
    ( r1_tmap_1(esk7_0,esk5_0,esk8_0,X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X2,esk5_0,k2_tmap_1(esk7_0,esk5_0,esk8_0,X2),X1)
    | ~ v1_tsep_1(X2,esk7_0)
    | ~ m1_pre_topc(X2,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_62]),c_0_63]),c_0_64]),c_0_53]),c_0_65]),c_0_54]),c_0_66])]),c_0_67]),c_0_68])).

cnf(c_0_144,negated_conjecture,
    ( r1_tmap_1(esk7_0,esk5_0,k2_tmap_1(esk7_0,esk5_0,esk8_0,esk7_0),esk9_0)
    | ~ v1_tsep_1(esk7_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_131]),c_0_45])]),c_0_68])).

cnf(c_0_145,negated_conjecture,
    ( ~ r1_tmap_1(esk7_0,esk5_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_146,negated_conjecture,
    ( v1_tsep_1(X1,esk7_0)
    | u1_struct_0(X2) != u1_struct_0(X1)
    | ~ v3_pre_topc(u1_struct_0(X2),esk7_0)
    | ~ m1_pre_topc(X1,esk7_0)
    | ~ m1_pre_topc(X2,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_142]),c_0_53]),c_0_54])])).

cnf(c_0_147,negated_conjecture,
    ( ~ v1_tsep_1(esk7_0,esk7_0)
    | ~ v1_tsep_1(esk7_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_144]),c_0_52]),c_0_131])]),c_0_145]),c_0_68])).

cnf(c_0_148,negated_conjecture,
    ( v1_tsep_1(X1,esk7_0)
    | u1_struct_0(esk7_0) != u1_struct_0(X1)
    | ~ v3_pre_topc(u1_struct_0(esk7_0),esk7_0)
    | ~ m1_pre_topc(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_75]),c_0_55])])).

cnf(c_0_149,negated_conjecture,
    ( ~ v1_tsep_1(esk7_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_138]),c_0_45])])).

cnf(c_0_150,negated_conjecture,
    ( v1_tsep_1(X1,esk7_0)
    | u1_struct_0(esk7_0) != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_133]),c_0_134]),c_0_54]),c_0_114])])).

cnf(c_0_151,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_150]),c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:01:53 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.35/0.53  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.35/0.53  # and selection function PSelectComplexExceptRRHorn.
% 0.35/0.53  #
% 0.35/0.53  # Preprocessing time       : 0.030 s
% 0.35/0.53  # Presaturation interreduction done
% 0.35/0.53  
% 0.35/0.53  # Proof found!
% 0.35/0.53  # SZS status Theorem
% 0.35/0.53  # SZS output start CNFRefutation
% 0.35/0.53  fof(t88_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=X4=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))=>r1_tmap_1(X4,X2,X5,X6)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 0.35/0.53  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.35/0.53  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.35/0.53  fof(t11_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))&m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 0.35/0.53  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.35/0.53  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.35/0.53  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.35/0.53  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.35/0.53  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.35/0.53  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.35/0.53  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.35/0.53  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.35/0.53  fof(t67_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:(((~(v2_struct_0(X4))&v1_tsep_1(X4,X2))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>(X5=X6=>(r1_tmap_1(X2,X1,X3,X5)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 0.35/0.53  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.35/0.53  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.35/0.53  fof(free_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3, X4]:(g1_pre_topc(X1,X2)=g1_pre_topc(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 0.35/0.53  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.35/0.53  fof(t16_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 0.35/0.53  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.35/0.53  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.35/0.53  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.35/0.53  fof(c_0_21, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=X4=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))=>r1_tmap_1(X4,X2,X5,X6))))))))))), inference(assume_negation,[status(cth)],[t88_tmap_1])).
% 0.35/0.53  fof(c_0_22, plain, ![X36, X37]:((~m1_pre_topc(X36,X37)|m1_pre_topc(X36,g1_pre_topc(u1_struct_0(X37),u1_pre_topc(X37)))|~l1_pre_topc(X37)|~l1_pre_topc(X36))&(~m1_pre_topc(X36,g1_pre_topc(u1_struct_0(X37),u1_pre_topc(X37)))|m1_pre_topc(X36,X37)|~l1_pre_topc(X37)|~l1_pre_topc(X36))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.35/0.53  fof(c_0_23, plain, ![X24, X25]:(~l1_pre_topc(X24)|(~m1_pre_topc(X25,X24)|l1_pre_topc(X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.35/0.53  fof(c_0_24, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&((~v2_struct_0(esk6_0)&m1_pre_topc(esk6_0,esk4_0))&((~v2_struct_0(esk7_0)&m1_pre_topc(esk7_0,esk4_0))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0)))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0)))))&(g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))=esk7_0&(m1_subset_1(esk9_0,u1_struct_0(esk7_0))&(m1_subset_1(esk10_0,u1_struct_0(esk6_0))&((esk9_0=esk10_0&r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk10_0))&~r1_tmap_1(esk7_0,esk5_0,esk8_0,esk9_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).
% 0.35/0.53  fof(c_0_25, plain, ![X47, X48]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X48),u1_pre_topc(X48)))|~m1_pre_topc(X48,X47)|~l1_pre_topc(X47))&(m1_pre_topc(g1_pre_topc(u1_struct_0(X48),u1_pre_topc(X48)),X47)|~m1_pre_topc(X48,X47)|~l1_pre_topc(X47))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).
% 0.35/0.53  cnf(c_0_26, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.35/0.53  cnf(c_0_27, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.35/0.53  cnf(c_0_28, negated_conjecture, (m1_pre_topc(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.35/0.53  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.35/0.53  cnf(c_0_30, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.35/0.53  cnf(c_0_31, negated_conjecture, (g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))=esk7_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.35/0.53  fof(c_0_32, plain, ![X54]:(~l1_pre_topc(X54)|m1_pre_topc(X54,X54)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.35/0.53  fof(c_0_33, plain, ![X55, X56, X57]:((~r1_tarski(u1_struct_0(X56),u1_struct_0(X57))|m1_pre_topc(X56,X57)|~m1_pre_topc(X57,X55)|~m1_pre_topc(X56,X55)|(~v2_pre_topc(X55)|~l1_pre_topc(X55)))&(~m1_pre_topc(X56,X57)|r1_tarski(u1_struct_0(X56),u1_struct_0(X57))|~m1_pre_topc(X57,X55)|~m1_pre_topc(X56,X55)|(~v2_pre_topc(X55)|~l1_pre_topc(X55)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.35/0.53  fof(c_0_34, plain, ![X64, X65, X66]:(~v2_pre_topc(X64)|~l1_pre_topc(X64)|(~m1_pre_topc(X65,X64)|(~m1_pre_topc(X66,X65)|m1_pre_topc(X66,X64)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.35/0.53  cnf(c_0_35, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_26, c_0_27])).
% 0.35/0.53  cnf(c_0_36, negated_conjecture, (l1_pre_topc(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.35/0.53  cnf(c_0_37, negated_conjecture, (m1_pre_topc(esk7_0,X1)|~m1_pre_topc(esk6_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.35/0.53  cnf(c_0_38, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.35/0.53  fof(c_0_39, plain, ![X13, X14]:(~v2_pre_topc(X13)|~l1_pre_topc(X13)|(~m1_pre_topc(X14,X13)|v2_pre_topc(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.35/0.53  fof(c_0_40, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.35/0.53  fof(c_0_41, plain, ![X10, X11]:((~m1_subset_1(X10,k1_zfmisc_1(X11))|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|m1_subset_1(X10,k1_zfmisc_1(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.35/0.53  cnf(c_0_42, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.35/0.53  cnf(c_0_43, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.35/0.53  cnf(c_0_44, negated_conjecture, (m1_pre_topc(X1,esk7_0)|~m1_pre_topc(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_31]), c_0_36])])).
% 0.35/0.53  cnf(c_0_45, negated_conjecture, (m1_pre_topc(esk7_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_36])])).
% 0.35/0.53  cnf(c_0_46, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.35/0.53  cnf(c_0_47, negated_conjecture, (m1_pre_topc(esk7_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.35/0.53  cnf(c_0_48, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.35/0.53  cnf(c_0_49, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.35/0.53  cnf(c_0_50, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.35/0.53  cnf(c_0_51, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(csr,[status(thm)],[c_0_42, c_0_43])).
% 0.35/0.53  cnf(c_0_52, negated_conjecture, (m1_pre_topc(esk7_0,esk7_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.35/0.53  cnf(c_0_53, negated_conjecture, (v2_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_29])])).
% 0.35/0.53  cnf(c_0_54, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_47]), c_0_29])])).
% 0.35/0.53  cnf(c_0_55, negated_conjecture, (m1_pre_topc(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_38]), c_0_36])])).
% 0.35/0.53  fof(c_0_56, plain, ![X38, X39, X40, X41]:(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|(~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X39))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X39))))|(~m1_pre_topc(X41,X38)|k2_tmap_1(X38,X39,X40,X41)=k2_partfun1(u1_struct_0(X38),u1_struct_0(X39),X40,u1_struct_0(X41)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.35/0.53  cnf(c_0_57, plain, (X1=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.35/0.53  cnf(c_0_58, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk7_0))|~m1_pre_topc(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54])])).
% 0.35/0.53  cnf(c_0_59, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.35/0.53  cnf(c_0_60, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk6_0))|~m1_pre_topc(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_55]), c_0_53]), c_0_54])])).
% 0.35/0.53  cnf(c_0_61, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.35/0.53  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.35/0.53  cnf(c_0_63, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.35/0.53  cnf(c_0_64, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.35/0.53  cnf(c_0_65, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.35/0.53  cnf(c_0_66, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.35/0.53  cnf(c_0_67, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.35/0.53  cnf(c_0_68, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.35/0.53  cnf(c_0_69, negated_conjecture, (u1_struct_0(esk7_0)=u1_struct_0(X1)|~m1_pre_topc(X1,esk7_0)|~m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.35/0.53  cnf(c_0_70, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk6_0)))|~m1_pre_topc(X1,esk6_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.35/0.53  fof(c_0_71, plain, ![X42, X43, X44, X45, X46]:(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)|(~m1_pre_topc(X44,X42)|(~m1_pre_topc(X45,X42)|(~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X43))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X43))))|(~m1_pre_topc(X45,X44)|k3_tmap_1(X42,X43,X44,X45,X46)=k2_partfun1(u1_struct_0(X44),u1_struct_0(X43),X46,u1_struct_0(X45)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.35/0.53  fof(c_0_72, plain, ![X58, X59, X60, X61, X62, X63]:((~r1_tmap_1(X59,X58,X60,X62)|r1_tmap_1(X61,X58,k2_tmap_1(X59,X58,X60,X61),X63)|X62!=X63|~m1_subset_1(X63,u1_struct_0(X61))|~m1_subset_1(X62,u1_struct_0(X59))|(v2_struct_0(X61)|~v1_tsep_1(X61,X59)|~m1_pre_topc(X61,X59))|(~v1_funct_1(X60)|~v1_funct_2(X60,u1_struct_0(X59),u1_struct_0(X58))|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X59),u1_struct_0(X58)))))|(v2_struct_0(X59)|~v2_pre_topc(X59)|~l1_pre_topc(X59))|(v2_struct_0(X58)|~v2_pre_topc(X58)|~l1_pre_topc(X58)))&(~r1_tmap_1(X61,X58,k2_tmap_1(X59,X58,X60,X61),X63)|r1_tmap_1(X59,X58,X60,X62)|X62!=X63|~m1_subset_1(X63,u1_struct_0(X61))|~m1_subset_1(X62,u1_struct_0(X59))|(v2_struct_0(X61)|~v1_tsep_1(X61,X59)|~m1_pre_topc(X61,X59))|(~v1_funct_1(X60)|~v1_funct_2(X60,u1_struct_0(X59),u1_struct_0(X58))|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X59),u1_struct_0(X58)))))|(v2_struct_0(X59)|~v2_pre_topc(X59)|~l1_pre_topc(X59))|(v2_struct_0(X58)|~v2_pre_topc(X58)|~l1_pre_topc(X58)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_tmap_1])])])])])).
% 0.35/0.53  fof(c_0_73, plain, ![X31, X32, X33]:(v2_struct_0(X31)|~l1_pre_topc(X31)|(v2_struct_0(X32)|~m1_pre_topc(X32,X31)|(~m1_subset_1(X33,u1_struct_0(X32))|m1_subset_1(X33,u1_struct_0(X31))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.35/0.53  cnf(c_0_74, negated_conjecture, (k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(X1))=k2_tmap_1(esk7_0,esk5_0,esk8_0,X1)|~m1_pre_topc(X1,esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_64]), c_0_65]), c_0_53]), c_0_66]), c_0_54])]), c_0_67]), c_0_68])).
% 0.35/0.53  cnf(c_0_75, negated_conjecture, (u1_struct_0(esk6_0)=u1_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_55]), c_0_45])])).
% 0.35/0.53  cnf(c_0_76, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.35/0.53  cnf(c_0_77, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.35/0.53  fof(c_0_78, plain, ![X26]:(~l1_pre_topc(X26)|m1_subset_1(u1_pre_topc(X26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.35/0.53  cnf(c_0_79, plain, (r1_tmap_1(X3,X2,X4,X6)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|X6!=X5|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X6,u1_struct_0(X3))|~v1_tsep_1(X1,X3)|~m1_pre_topc(X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.35/0.53  cnf(c_0_80, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.35/0.53  cnf(c_0_81, negated_conjecture, (v2_pre_topc(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_28]), c_0_48]), c_0_29])])).
% 0.35/0.53  cnf(c_0_82, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.35/0.53  cnf(c_0_83, negated_conjecture, (k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(esk7_0))=k2_tmap_1(esk7_0,esk5_0,esk8_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_55])])).
% 0.35/0.53  cnf(c_0_84, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.35/0.53  cnf(c_0_85, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_76])).
% 0.35/0.53  cnf(c_0_86, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(csr,[status(thm)],[c_0_77, c_0_43])).
% 0.35/0.53  fof(c_0_87, plain, ![X27, X28, X29, X30]:((X27=X29|g1_pre_topc(X27,X28)!=g1_pre_topc(X29,X30)|~m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X27))))&(X28=X30|g1_pre_topc(X27,X28)!=g1_pre_topc(X29,X30)|~m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).
% 0.35/0.53  cnf(c_0_88, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.35/0.53  fof(c_0_89, plain, ![X12]:(~l1_pre_topc(X12)|(~v1_pre_topc(X12)|X12=g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.35/0.53  cnf(c_0_90, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.35/0.53  cnf(c_0_91, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X5)|~r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)|~v1_tsep_1(X5,X1)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~m1_pre_topc(X5,X1)|~v2_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,u1_struct_0(X5))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_79]), c_0_80])).
% 0.35/0.53  cnf(c_0_92, negated_conjecture, (k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(X1),X2,u1_struct_0(X3))=k2_tmap_1(esk6_0,X1,X2,X3)|v2_struct_0(X1)|~v1_funct_2(X2,u1_struct_0(esk7_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_pre_topc(X3,esk6_0)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(X1))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_75]), c_0_81]), c_0_36])]), c_0_82])).
% 0.35/0.53  cnf(c_0_93, negated_conjecture, (k2_tmap_1(esk7_0,esk5_0,esk8_0,esk6_0)=k2_tmap_1(esk7_0,esk5_0,esk8_0,esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_83]), c_0_63]), c_0_64]), c_0_52]), c_0_65]), c_0_53]), c_0_66]), c_0_54]), c_0_62])]), c_0_67]), c_0_68])).
% 0.35/0.53  cnf(c_0_94, plain, (m1_pre_topc(X1,X1)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.35/0.53  cnf(c_0_95, negated_conjecture, (k3_tmap_1(X1,esk5_0,esk7_0,X2,esk8_0)=k2_tmap_1(esk7_0,esk5_0,esk8_0,X2)|v2_struct_0(X1)|~m1_pre_topc(X2,esk7_0)|~m1_pre_topc(esk7_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_74]), c_0_63]), c_0_64]), c_0_65]), c_0_66]), c_0_62])]), c_0_67])).
% 0.35/0.53  cnf(c_0_96, negated_conjecture, (m1_pre_topc(esk6_0,X1)|~m1_pre_topc(esk7_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_43, c_0_55])).
% 0.35/0.53  fof(c_0_97, plain, ![X49, X50, X51]:((~v1_tsep_1(X50,X49)|~m1_pre_topc(X50,X49)|v3_pre_topc(X51,X49)|X51!=u1_struct_0(X50)|~m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))|~m1_pre_topc(X50,X49)|(~v2_pre_topc(X49)|~l1_pre_topc(X49)))&((v1_tsep_1(X50,X49)|~v3_pre_topc(X51,X49)|X51!=u1_struct_0(X50)|~m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))|~m1_pre_topc(X50,X49)|(~v2_pre_topc(X49)|~l1_pre_topc(X49)))&(m1_pre_topc(X50,X49)|~v3_pre_topc(X51,X49)|X51!=u1_struct_0(X50)|~m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))|~m1_pre_topc(X50,X49)|(~v2_pre_topc(X49)|~l1_pre_topc(X49))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).
% 0.35/0.53  fof(c_0_98, plain, ![X15, X16, X17, X18]:((((r2_hidden(u1_struct_0(X15),u1_pre_topc(X15))|~v2_pre_topc(X15)|~l1_pre_topc(X15))&(~m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))|(~r1_tarski(X16,u1_pre_topc(X15))|r2_hidden(k5_setfam_1(u1_struct_0(X15),X16),u1_pre_topc(X15)))|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X15)))|(~r2_hidden(X17,u1_pre_topc(X15))|~r2_hidden(X18,u1_pre_topc(X15))|r2_hidden(k9_subset_1(u1_struct_0(X15),X17,X18),u1_pre_topc(X15))))|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(((m1_subset_1(esk2_1(X15),k1_zfmisc_1(u1_struct_0(X15)))|(m1_subset_1(esk1_1(X15),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))|~r2_hidden(u1_struct_0(X15),u1_pre_topc(X15)))|v2_pre_topc(X15)|~l1_pre_topc(X15))&((m1_subset_1(esk3_1(X15),k1_zfmisc_1(u1_struct_0(X15)))|(m1_subset_1(esk1_1(X15),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))|~r2_hidden(u1_struct_0(X15),u1_pre_topc(X15)))|v2_pre_topc(X15)|~l1_pre_topc(X15))&(((r2_hidden(esk2_1(X15),u1_pre_topc(X15))|(m1_subset_1(esk1_1(X15),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))|~r2_hidden(u1_struct_0(X15),u1_pre_topc(X15)))|v2_pre_topc(X15)|~l1_pre_topc(X15))&(r2_hidden(esk3_1(X15),u1_pre_topc(X15))|(m1_subset_1(esk1_1(X15),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))|~r2_hidden(u1_struct_0(X15),u1_pre_topc(X15)))|v2_pre_topc(X15)|~l1_pre_topc(X15)))&(~r2_hidden(k9_subset_1(u1_struct_0(X15),esk2_1(X15),esk3_1(X15)),u1_pre_topc(X15))|(m1_subset_1(esk1_1(X15),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))|~r2_hidden(u1_struct_0(X15),u1_pre_topc(X15)))|v2_pre_topc(X15)|~l1_pre_topc(X15)))))&(((m1_subset_1(esk2_1(X15),k1_zfmisc_1(u1_struct_0(X15)))|(r1_tarski(esk1_1(X15),u1_pre_topc(X15))|~r2_hidden(u1_struct_0(X15),u1_pre_topc(X15)))|v2_pre_topc(X15)|~l1_pre_topc(X15))&((m1_subset_1(esk3_1(X15),k1_zfmisc_1(u1_struct_0(X15)))|(r1_tarski(esk1_1(X15),u1_pre_topc(X15))|~r2_hidden(u1_struct_0(X15),u1_pre_topc(X15)))|v2_pre_topc(X15)|~l1_pre_topc(X15))&(((r2_hidden(esk2_1(X15),u1_pre_topc(X15))|(r1_tarski(esk1_1(X15),u1_pre_topc(X15))|~r2_hidden(u1_struct_0(X15),u1_pre_topc(X15)))|v2_pre_topc(X15)|~l1_pre_topc(X15))&(r2_hidden(esk3_1(X15),u1_pre_topc(X15))|(r1_tarski(esk1_1(X15),u1_pre_topc(X15))|~r2_hidden(u1_struct_0(X15),u1_pre_topc(X15)))|v2_pre_topc(X15)|~l1_pre_topc(X15)))&(~r2_hidden(k9_subset_1(u1_struct_0(X15),esk2_1(X15),esk3_1(X15)),u1_pre_topc(X15))|(r1_tarski(esk1_1(X15),u1_pre_topc(X15))|~r2_hidden(u1_struct_0(X15),u1_pre_topc(X15)))|v2_pre_topc(X15)|~l1_pre_topc(X15)))))&((m1_subset_1(esk2_1(X15),k1_zfmisc_1(u1_struct_0(X15)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X15),esk1_1(X15)),u1_pre_topc(X15))|~r2_hidden(u1_struct_0(X15),u1_pre_topc(X15)))|v2_pre_topc(X15)|~l1_pre_topc(X15))&((m1_subset_1(esk3_1(X15),k1_zfmisc_1(u1_struct_0(X15)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X15),esk1_1(X15)),u1_pre_topc(X15))|~r2_hidden(u1_struct_0(X15),u1_pre_topc(X15)))|v2_pre_topc(X15)|~l1_pre_topc(X15))&(((r2_hidden(esk2_1(X15),u1_pre_topc(X15))|(~r2_hidden(k5_setfam_1(u1_struct_0(X15),esk1_1(X15)),u1_pre_topc(X15))|~r2_hidden(u1_struct_0(X15),u1_pre_topc(X15)))|v2_pre_topc(X15)|~l1_pre_topc(X15))&(r2_hidden(esk3_1(X15),u1_pre_topc(X15))|(~r2_hidden(k5_setfam_1(u1_struct_0(X15),esk1_1(X15)),u1_pre_topc(X15))|~r2_hidden(u1_struct_0(X15),u1_pre_topc(X15)))|v2_pre_topc(X15)|~l1_pre_topc(X15)))&(~r2_hidden(k9_subset_1(u1_struct_0(X15),esk2_1(X15),esk3_1(X15)),u1_pre_topc(X15))|(~r2_hidden(k5_setfam_1(u1_struct_0(X15),esk1_1(X15)),u1_pre_topc(X15))|~r2_hidden(u1_struct_0(X15),u1_pre_topc(X15)))|v2_pre_topc(X15)|~l1_pre_topc(X15)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.35/0.53  cnf(c_0_99, plain, (X1=X2|g1_pre_topc(X3,X1)!=g1_pre_topc(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.35/0.53  cnf(c_0_100, negated_conjecture, (m1_subset_1(u1_pre_topc(esk6_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_75]), c_0_36])])).
% 0.35/0.53  cnf(c_0_101, negated_conjecture, (g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk6_0))=esk7_0), inference(rw,[status(thm)],[c_0_31, c_0_75])).
% 0.35/0.53  cnf(c_0_102, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.35/0.53  cnf(c_0_103, negated_conjecture, (v1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_28]), c_0_31]), c_0_29])])).
% 0.35/0.53  fof(c_0_104, plain, ![X34, X35]:(~l1_pre_topc(X34)|(~m1_pre_topc(X35,g1_pre_topc(u1_struct_0(X34),u1_pre_topc(X34)))|m1_pre_topc(X35,X34))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.35/0.53  cnf(c_0_105, negated_conjecture, (r1_tmap_1(esk6_0,X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X4)|~r1_tmap_1(X4,X1,k2_tmap_1(esk6_0,X1,X2,X4),X3)|~v1_tsep_1(X4,esk6_0)|~v1_funct_2(X2,u1_struct_0(esk7_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_pre_topc(X4,esk6_0)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(X1))))|~m1_subset_1(X3,u1_struct_0(X4))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_75]), c_0_81]), c_0_36])]), c_0_82])).
% 0.35/0.53  cnf(c_0_106, negated_conjecture, (k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(X1))=k2_tmap_1(esk6_0,esk5_0,esk8_0,X1)|~m1_pre_topc(X1,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_62]), c_0_63]), c_0_64]), c_0_65]), c_0_66])]), c_0_67])).
% 0.35/0.53  cnf(c_0_107, negated_conjecture, (k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk5_0),esk8_0,u1_struct_0(esk7_0))=k2_tmap_1(esk7_0,esk5_0,esk8_0,esk7_0)), inference(rw,[status(thm)],[c_0_83, c_0_93])).
% 0.35/0.53  cnf(c_0_108, negated_conjecture, (m1_pre_topc(esk6_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_55]), c_0_53]), c_0_54])])).
% 0.35/0.53  cnf(c_0_109, negated_conjecture, (r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk10_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.35/0.53  cnf(c_0_110, negated_conjecture, (esk9_0=esk10_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.35/0.53  cnf(c_0_111, negated_conjecture, (k3_tmap_1(X1,esk5_0,esk7_0,esk6_0,esk8_0)=k2_tmap_1(esk7_0,esk5_0,esk8_0,esk7_0)|v2_struct_0(X1)|~m1_pre_topc(esk7_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_93]), c_0_52]), c_0_53]), c_0_54])])).
% 0.35/0.53  cnf(c_0_112, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.35/0.53  cnf(c_0_113, plain, (v1_tsep_1(X1,X2)|~v3_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.35/0.53  cnf(c_0_114, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_59, c_0_85])).
% 0.35/0.53  cnf(c_0_115, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.35/0.53  cnf(c_0_116, negated_conjecture, (u1_pre_topc(esk6_0)=X1|g1_pre_topc(X2,X1)!=esk7_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_101])).
% 0.35/0.53  cnf(c_0_117, negated_conjecture, (g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_54])])).
% 0.35/0.53  cnf(c_0_118, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_104])).
% 0.35/0.53  cnf(c_0_119, negated_conjecture, (r1_tmap_1(esk6_0,esk5_0,esk8_0,X1)|v2_struct_0(X2)|~r1_tmap_1(X2,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk8_0,X2),X1)|~v1_tsep_1(X2,esk6_0)|~m1_pre_topc(X2,esk6_0)|~m1_subset_1(X1,u1_struct_0(X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_62]), c_0_63]), c_0_64]), c_0_65]), c_0_66])]), c_0_67])).
% 0.35/0.53  cnf(c_0_120, negated_conjecture, (k2_tmap_1(esk6_0,esk5_0,esk8_0,esk6_0)=k2_tmap_1(esk7_0,esk5_0,esk8_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_75]), c_0_107]), c_0_108])])).
% 0.35/0.53  cnf(c_0_121, negated_conjecture, (r1_tmap_1(esk6_0,esk5_0,k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0),esk9_0)), inference(rw,[status(thm)],[c_0_109, c_0_110])).
% 0.35/0.53  cnf(c_0_122, negated_conjecture, (k3_tmap_1(esk4_0,esk5_0,esk7_0,esk6_0,esk8_0)=k2_tmap_1(esk7_0,esk5_0,esk8_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_47]), c_0_48]), c_0_29])]), c_0_112])).
% 0.35/0.53  cnf(c_0_123, plain, (v1_tsep_1(X1,X2)|u1_struct_0(X2)!=u1_struct_0(X1)|~v3_pre_topc(u1_struct_0(X2),X2)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 0.35/0.53  fof(c_0_124, plain, ![X22, X23]:((~v3_pre_topc(X23,X22)|r2_hidden(X23,u1_pre_topc(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22))&(~r2_hidden(X23,u1_pre_topc(X22))|v3_pre_topc(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.35/0.53  cnf(c_0_125, negated_conjecture, (r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_75]), c_0_81]), c_0_36])])).
% 0.35/0.53  cnf(c_0_126, negated_conjecture, (u1_pre_topc(esk6_0)=u1_pre_topc(esk7_0)), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 0.35/0.53  cnf(c_0_127, plain, (r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X6)|v2_struct_0(X5)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tmap_1(X1,X2,X3,X4)|X4!=X6|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X4,u1_struct_0(X1))|~v1_tsep_1(X5,X1)|~m1_pre_topc(X5,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.35/0.53  cnf(c_0_128, negated_conjecture, (m1_pre_topc(X1,esk6_0)|~m1_pre_topc(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_31]), c_0_36])])).
% 0.35/0.53  cnf(c_0_129, negated_conjecture, (r1_tmap_1(esk6_0,esk5_0,esk8_0,X1)|~r1_tmap_1(esk6_0,esk5_0,k2_tmap_1(esk7_0,esk5_0,esk8_0,esk7_0),X1)|~v1_tsep_1(esk6_0,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_108]), c_0_75])]), c_0_82])).
% 0.35/0.53  cnf(c_0_130, negated_conjecture, (r1_tmap_1(esk6_0,esk5_0,k2_tmap_1(esk7_0,esk5_0,esk8_0,esk7_0),esk9_0)), inference(rw,[status(thm)],[c_0_121, c_0_122])).
% 0.35/0.53  cnf(c_0_131, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.35/0.53  cnf(c_0_132, negated_conjecture, (v1_tsep_1(X1,esk6_0)|u1_struct_0(esk7_0)!=u1_struct_0(X1)|~v3_pre_topc(u1_struct_0(esk7_0),esk6_0)|~m1_pre_topc(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_75]), c_0_81]), c_0_36])])).
% 0.35/0.53  cnf(c_0_133, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_124])).
% 0.35/0.53  cnf(c_0_134, negated_conjecture, (r2_hidden(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))), inference(rw,[status(thm)],[c_0_125, c_0_126])).
% 0.35/0.53  cnf(c_0_135, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X3,X2,X4,X5)|~v1_tsep_1(X1,X3)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X4)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X5,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_127]), c_0_80])).
% 0.35/0.53  cnf(c_0_136, negated_conjecture, (k2_tmap_1(esk6_0,esk5_0,esk8_0,X1)=k2_tmap_1(esk7_0,esk5_0,esk8_0,X1)|~m1_pre_topc(X1,esk7_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_106]), c_0_63]), c_0_64]), c_0_65]), c_0_53]), c_0_66]), c_0_54]), c_0_62])]), c_0_67]), c_0_68]), c_0_128])).
% 0.35/0.53  cnf(c_0_137, negated_conjecture, (r1_tmap_1(esk6_0,esk5_0,esk8_0,esk9_0)|~v1_tsep_1(esk6_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_131])])).
% 0.35/0.53  cnf(c_0_138, negated_conjecture, (v1_tsep_1(X1,esk6_0)|u1_struct_0(esk7_0)!=u1_struct_0(X1)|~m1_pre_topc(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_133]), c_0_126]), c_0_134]), c_0_36]), c_0_75]), c_0_114])])).
% 0.35/0.53  cnf(c_0_139, negated_conjecture, (r1_tmap_1(X1,esk5_0,k2_tmap_1(esk7_0,esk5_0,esk8_0,X1),X2)|v2_struct_0(X1)|~r1_tmap_1(esk6_0,esk5_0,esk8_0,X2)|~v1_tsep_1(X1,esk6_0)|~m1_pre_topc(X1,esk6_0)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_136]), c_0_75]), c_0_63]), c_0_64]), c_0_65]), c_0_81]), c_0_66]), c_0_36]), c_0_75]), c_0_62])]), c_0_82]), c_0_67]), c_0_44])).
% 0.35/0.53  cnf(c_0_140, negated_conjecture, (r1_tmap_1(esk6_0,esk5_0,esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_138]), c_0_75]), c_0_108])])).
% 0.35/0.53  cnf(c_0_141, negated_conjecture, (r1_tmap_1(X1,esk5_0,k2_tmap_1(esk7_0,esk5_0,esk8_0,X1),esk9_0)|v2_struct_0(X1)|~v1_tsep_1(X1,esk6_0)|~m1_pre_topc(X1,esk6_0)|~m1_subset_1(esk9_0,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_139, c_0_140])).
% 0.35/0.53  cnf(c_0_142, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk7_0)))|~m1_pre_topc(X1,esk7_0)), inference(spm,[status(thm)],[c_0_59, c_0_58])).
% 0.35/0.53  cnf(c_0_143, negated_conjecture, (r1_tmap_1(esk7_0,esk5_0,esk8_0,X1)|v2_struct_0(X2)|~r1_tmap_1(X2,esk5_0,k2_tmap_1(esk7_0,esk5_0,esk8_0,X2),X1)|~v1_tsep_1(X2,esk7_0)|~m1_pre_topc(X2,esk7_0)|~m1_subset_1(X1,u1_struct_0(X2))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_62]), c_0_63]), c_0_64]), c_0_53]), c_0_65]), c_0_54]), c_0_66])]), c_0_67]), c_0_68])).
% 0.35/0.53  cnf(c_0_144, negated_conjecture, (r1_tmap_1(esk7_0,esk5_0,k2_tmap_1(esk7_0,esk5_0,esk8_0,esk7_0),esk9_0)|~v1_tsep_1(esk7_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_131]), c_0_45])]), c_0_68])).
% 0.35/0.53  cnf(c_0_145, negated_conjecture, (~r1_tmap_1(esk7_0,esk5_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.35/0.53  cnf(c_0_146, negated_conjecture, (v1_tsep_1(X1,esk7_0)|u1_struct_0(X2)!=u1_struct_0(X1)|~v3_pre_topc(u1_struct_0(X2),esk7_0)|~m1_pre_topc(X1,esk7_0)|~m1_pre_topc(X2,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_142]), c_0_53]), c_0_54])])).
% 0.35/0.53  cnf(c_0_147, negated_conjecture, (~v1_tsep_1(esk7_0,esk7_0)|~v1_tsep_1(esk7_0,esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_144]), c_0_52]), c_0_131])]), c_0_145]), c_0_68])).
% 0.35/0.53  cnf(c_0_148, negated_conjecture, (v1_tsep_1(X1,esk7_0)|u1_struct_0(esk7_0)!=u1_struct_0(X1)|~v3_pre_topc(u1_struct_0(esk7_0),esk7_0)|~m1_pre_topc(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_75]), c_0_55])])).
% 0.35/0.53  cnf(c_0_149, negated_conjecture, (~v1_tsep_1(esk7_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_138]), c_0_45])])).
% 0.35/0.53  cnf(c_0_150, negated_conjecture, (v1_tsep_1(X1,esk7_0)|u1_struct_0(esk7_0)!=u1_struct_0(X1)|~m1_pre_topc(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_133]), c_0_134]), c_0_54]), c_0_114])])).
% 0.35/0.53  cnf(c_0_151, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_150]), c_0_52])]), ['proof']).
% 0.35/0.53  # SZS output end CNFRefutation
% 0.35/0.53  # Proof object total steps             : 152
% 0.35/0.53  # Proof object clause steps            : 109
% 0.35/0.53  # Proof object formula steps           : 43
% 0.35/0.53  # Proof object conjectures             : 77
% 0.35/0.53  # Proof object clause conjectures      : 74
% 0.35/0.53  # Proof object formula conjectures     : 3
% 0.35/0.53  # Proof object initial clauses used    : 43
% 0.35/0.53  # Proof object initial formulas used   : 21
% 0.35/0.53  # Proof object generating inferences   : 55
% 0.35/0.53  # Proof object simplifying inferences  : 187
% 0.35/0.53  # Training examples: 0 positive, 0 negative
% 0.35/0.53  # Parsed axioms                        : 22
% 0.35/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.35/0.53  # Initial clauses                      : 68
% 0.35/0.53  # Removed in clause preprocessing      : 1
% 0.35/0.53  # Initial clauses in saturation        : 67
% 0.35/0.53  # Processed clauses                    : 1520
% 0.35/0.53  # ...of these trivial                  : 27
% 0.35/0.53  # ...subsumed                          : 858
% 0.35/0.53  # ...remaining for further processing  : 635
% 0.35/0.53  # Other redundant clauses eliminated   : 10
% 0.35/0.53  # Clauses deleted for lack of memory   : 0
% 0.35/0.53  # Backward-subsumed                    : 26
% 0.35/0.53  # Backward-rewritten                   : 17
% 0.35/0.53  # Generated clauses                    : 5578
% 0.35/0.53  # ...of the previous two non-trivial   : 4542
% 0.35/0.53  # Contextual simplify-reflections      : 79
% 0.35/0.53  # Paramodulations                      : 5497
% 0.35/0.53  # Factorizations                       : 8
% 0.35/0.53  # Equation resolutions                 : 73
% 0.35/0.53  # Propositional unsat checks           : 0
% 0.35/0.53  #    Propositional check models        : 0
% 0.35/0.53  #    Propositional check unsatisfiable : 0
% 0.35/0.53  #    Propositional clauses             : 0
% 0.35/0.53  #    Propositional clauses after purity: 0
% 0.35/0.53  #    Propositional unsat core size     : 0
% 0.35/0.53  #    Propositional preprocessing time  : 0.000
% 0.35/0.53  #    Propositional encoding time       : 0.000
% 0.35/0.53  #    Propositional solver time         : 0.000
% 0.35/0.53  #    Success case prop preproc time    : 0.000
% 0.35/0.53  #    Success case prop encoding time   : 0.000
% 0.35/0.53  #    Success case prop solver time     : 0.000
% 0.35/0.53  # Current number of processed clauses  : 523
% 0.35/0.53  #    Positive orientable unit clauses  : 44
% 0.35/0.53  #    Positive unorientable unit clauses: 0
% 0.35/0.53  #    Negative unit clauses             : 7
% 0.35/0.53  #    Non-unit-clauses                  : 472
% 0.35/0.53  # Current number of unprocessed clauses: 2664
% 0.35/0.53  # ...number of literals in the above   : 19682
% 0.35/0.53  # Current number of archived formulas  : 0
% 0.35/0.53  # Current number of archived clauses   : 108
% 0.35/0.53  # Clause-clause subsumption calls (NU) : 78992
% 0.35/0.53  # Rec. Clause-clause subsumption calls : 13425
% 0.35/0.53  # Non-unit clause-clause subsumptions  : 942
% 0.35/0.53  # Unit Clause-clause subsumption calls : 1293
% 0.35/0.53  # Rewrite failures with RHS unbound    : 0
% 0.35/0.53  # BW rewrite match attempts            : 39
% 0.35/0.53  # BW rewrite match successes           : 9
% 0.35/0.53  # Condensation attempts                : 0
% 0.35/0.53  # Condensation successes               : 0
% 0.35/0.53  # Termbank termtop insertions          : 158617
% 0.35/0.53  
% 0.35/0.53  # -------------------------------------------------
% 0.35/0.53  # User time                : 0.178 s
% 0.35/0.53  # System time              : 0.012 s
% 0.35/0.53  # Total time               : 0.190 s
% 0.35/0.53  # Maximum resident set size: 1616 pages
%------------------------------------------------------------------------------
