%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:48 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  144 (1979 expanded)
%              Number of clauses        :  103 ( 709 expanded)
%              Number of leaves         :   20 ( 473 expanded)
%              Depth                    :   20
%              Number of atoms          :  743 (27231 expanded)
%              Number of equality atoms :   37 (1141 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_connsp_2(X3,X1,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                    & v3_pre_topc(X4,X1)
                    & r1_tarski(X4,X3)
                    & r2_hidden(X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t85_tmap_1,conjecture,(
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
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X2) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) )
                     => ( m1_pre_topc(X3,X4)
                       => ! [X6] :
                            ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X4))
                               => ! [X8] :
                                    ( m1_subset_1(X8,u1_struct_0(X3))
                                   => ( ( v3_pre_topc(X6,X2)
                                        & r2_hidden(X7,X6)
                                        & r1_tarski(X6,u1_struct_0(X3))
                                        & X7 = X8 )
                                     => ( r1_tmap_1(X4,X1,X5,X7)
                                      <=> r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,X4,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tmap_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(dt_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ! [X3] :
          ( m1_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

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

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(t33_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( v3_pre_topc(X2,X1)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
                   => ( X4 = X2
                     => v3_pre_topc(X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

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

fof(t65_tmap_1,axiom,(
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
                    & m1_pre_topc(X4,X2) )
                 => ! [X5] :
                      ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X2))
                         => ! [X7] :
                              ( m1_subset_1(X7,u1_struct_0(X4))
                             => ( ( r1_tarski(X5,u1_struct_0(X4))
                                  & m1_connsp_2(X5,X2,X6)
                                  & X6 = X7 )
                               => ( r1_tmap_1(X2,X1,X3,X6)
                                <=> r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X7) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).

fof(t64_tmap_1,axiom,(
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
                    & m1_pre_topc(X4,X2) )
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X4))
                         => ( ( X5 = X6
                              & r1_tmap_1(X2,X1,X3,X5) )
                           => r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

fof(c_0_20,plain,(
    ! [X48,X49,X50,X52] :
      ( ( m1_subset_1(esk3_3(X48,X49,X50),k1_zfmisc_1(u1_struct_0(X48)))
        | ~ m1_connsp_2(X50,X48,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X48)))
        | ~ m1_subset_1(X49,u1_struct_0(X48))
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) )
      & ( v3_pre_topc(esk3_3(X48,X49,X50),X48)
        | ~ m1_connsp_2(X50,X48,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X48)))
        | ~ m1_subset_1(X49,u1_struct_0(X48))
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) )
      & ( r1_tarski(esk3_3(X48,X49,X50),X50)
        | ~ m1_connsp_2(X50,X48,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X48)))
        | ~ m1_subset_1(X49,u1_struct_0(X48))
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) )
      & ( r2_hidden(X49,esk3_3(X48,X49,X50))
        | ~ m1_connsp_2(X50,X48,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X48)))
        | ~ m1_subset_1(X49,u1_struct_0(X48))
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) )
      & ( ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X48)))
        | ~ v3_pre_topc(X52,X48)
        | ~ r1_tarski(X52,X50)
        | ~ r2_hidden(X49,X52)
        | m1_connsp_2(X50,X48,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X48)))
        | ~ m1_subset_1(X49,u1_struct_0(X48))
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_connsp_2])])])])])])).

fof(c_0_21,plain,(
    ! [X28,X29,X30] :
      ( ~ r2_hidden(X28,X29)
      | ~ m1_subset_1(X29,k1_zfmisc_1(X30))
      | m1_subset_1(X28,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_22,negated_conjecture,(
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
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X2) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) )
                       => ( m1_pre_topc(X3,X4)
                         => ! [X6] :
                              ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X4))
                                 => ! [X8] :
                                      ( m1_subset_1(X8,u1_struct_0(X3))
                                     => ( ( v3_pre_topc(X6,X2)
                                          & r2_hidden(X7,X6)
                                          & r1_tarski(X6,u1_struct_0(X3))
                                          & X7 = X8 )
                                       => ( r1_tmap_1(X4,X1,X5,X7)
                                        <=> r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,X4,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t85_tmap_1])).

cnf(c_0_23,plain,
    ( m1_connsp_2(X3,X2,X4)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & ~ v2_struct_0(esk6_0)
    & m1_pre_topc(esk6_0,esk5_0)
    & ~ v2_struct_0(esk7_0)
    & m1_pre_topc(esk7_0,esk5_0)
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk4_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk4_0))))
    & m1_pre_topc(esk6_0,esk7_0)
    & m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & m1_subset_1(esk10_0,u1_struct_0(esk7_0))
    & m1_subset_1(esk11_0,u1_struct_0(esk6_0))
    & v3_pre_topc(esk9_0,esk5_0)
    & r2_hidden(esk10_0,esk9_0)
    & r1_tarski(esk9_0,u1_struct_0(esk6_0))
    & esk10_0 = esk11_0
    & ( ~ r1_tmap_1(esk7_0,esk4_0,esk8_0,esk10_0)
      | ~ r1_tmap_1(esk6_0,esk4_0,k3_tmap_1(esk5_0,esk4_0,esk7_0,esk6_0,esk8_0),esk11_0) )
    & ( r1_tmap_1(esk7_0,esk4_0,esk8_0,esk10_0)
      | r1_tmap_1(esk6_0,esk4_0,k3_tmap_1(esk5_0,esk4_0,esk7_0,esk6_0,esk8_0),esk11_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).

cnf(c_0_26,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X4,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X4)
    | ~ r1_tarski(X4,X1) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( v3_pre_topc(esk9_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_33,plain,(
    ! [X38,X39,X40] :
      ( v2_struct_0(X38)
      | ~ l1_pre_topc(X38)
      | v2_struct_0(X39)
      | ~ m1_pre_topc(X39,X38)
      | ~ m1_subset_1(X40,u1_struct_0(X39))
      | m1_subset_1(X40,u1_struct_0(X38)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

fof(c_0_34,plain,(
    ! [X45,X46,X47] :
      ( v2_struct_0(X45)
      | ~ v2_pre_topc(X45)
      | ~ l1_pre_topc(X45)
      | ~ m1_subset_1(X46,u1_struct_0(X45))
      | ~ m1_connsp_2(X47,X45,X46)
      | m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

cnf(c_0_35,negated_conjecture,
    ( m1_connsp_2(X1,esk5_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r2_hidden(X2,esk9_0)
    | ~ r1_tarski(esk9_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk10_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_41,plain,(
    ! [X62,X63,X64] :
      ( ( ~ r1_tarski(u1_struct_0(X63),u1_struct_0(X64))
        | m1_pre_topc(X63,X64)
        | ~ m1_pre_topc(X64,X62)
        | ~ m1_pre_topc(X63,X62)
        | ~ v2_pre_topc(X62)
        | ~ l1_pre_topc(X62) )
      & ( ~ m1_pre_topc(X63,X64)
        | r1_tarski(u1_struct_0(X63),u1_struct_0(X64))
        | ~ m1_pre_topc(X64,X62)
        | ~ m1_pre_topc(X63,X62)
        | ~ v2_pre_topc(X62)
        | ~ l1_pre_topc(X62) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

fof(c_0_42,plain,(
    ! [X78,X79,X80] :
      ( ~ v2_pre_topc(X78)
      | ~ l1_pre_topc(X78)
      | ~ m1_pre_topc(X79,X78)
      | ~ m1_pre_topc(X80,X79)
      | m1_pre_topc(X80,X78) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_43,plain,(
    ! [X17,X18,X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X19,X18)
        | r1_tarski(X19,X17)
        | X18 != k1_zfmisc_1(X17) )
      & ( ~ r1_tarski(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k1_zfmisc_1(X17) )
      & ( ~ r2_hidden(esk2_2(X21,X22),X22)
        | ~ r1_tarski(esk2_2(X21,X22),X21)
        | X22 = k1_zfmisc_1(X21) )
      & ( r2_hidden(esk2_2(X21,X22),X22)
        | r1_tarski(esk2_2(X21,X22),X21)
        | X22 = k1_zfmisc_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_44,plain,
    ( r1_tarski(esk3_3(X1,X2,X3),X3)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( m1_connsp_2(X1,esk5_0,esk10_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(esk9_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_28])]),c_0_40]),c_0_31])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk10_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_50,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | r1_tarski(esk3_3(X1,X2,X3),X3)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( m1_connsp_2(esk9_0,esk5_0,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_30])])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk10_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3) ),
    inference(csr,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_57,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk1_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk3_3(esk5_0,esk10_0,esk9_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_28]),c_0_29]),c_0_55])]),c_0_31])).

fof(c_0_60,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | r1_tarski(k1_zfmisc_1(X24),k1_zfmisc_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk7_0))
    | ~ m1_pre_topc(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_39]),c_0_28]),c_0_29])])).

cnf(c_0_62,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_63,plain,(
    ! [X41,X42,X43,X44] :
      ( ~ l1_pre_topc(X41)
      | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
      | ~ m1_pre_topc(X43,X41)
      | ~ v3_pre_topc(X42,X41)
      | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))
      | X44 != X42
      | v3_pre_topc(X44,X43) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_tops_2])])])).

fof(c_0_64,plain,(
    ! [X35,X36,X37] :
      ( ~ l1_pre_topc(X35)
      | ~ m1_pre_topc(X36,X35)
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
      | m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

cnf(c_0_65,plain,
    ( v3_pre_topc(esk3_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_66,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk10_0,esk9_0),k1_zfmisc_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk9_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk6_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_71,plain,
    ( v3_pre_topc(X4,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | X4 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_73,plain,
    ( v3_pre_topc(esk3_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_65,c_0_45])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk10_0,esk9_0),X1)
    | ~ r1_tarski(k1_zfmisc_1(esk9_0),X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(esk9_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

fof(c_0_76,plain,(
    ! [X26,X27] :
      ( ~ r2_hidden(X26,X27)
      | m1_subset_1(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(u1_struct_0(esk6_0)),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_70])).

cnf(c_0_78,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v3_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_71]),c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( v3_pre_topc(esk3_3(esk5_0,esk10_0,esk9_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_54]),c_0_28]),c_0_29]),c_0_55])]),c_0_31])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk10_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_81,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(k1_zfmisc_1(u1_struct_0(esk6_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_77])).

fof(c_0_83,plain,(
    ! [X33,X34] :
      ( ~ l1_pre_topc(X33)
      | ~ m1_pre_topc(X34,X33)
      | l1_pre_topc(X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_84,plain,(
    ! [X31,X32] :
      ( ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | ~ m1_pre_topc(X32,X31)
      | v2_pre_topc(X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_85,negated_conjecture,
    ( v3_pre_topc(esk3_3(esk5_0,esk10_0,esk9_0),X1)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(esk3_3(esk5_0,esk10_0,esk9_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_28])])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk3_3(esk5_0,esk10_0,esk9_0),X1)
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(esk6_0)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(k1_zfmisc_1(u1_struct_0(esk6_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

fof(c_0_88,plain,(
    ! [X57,X58,X59,X60,X61] :
      ( v2_struct_0(X57)
      | ~ v2_pre_topc(X57)
      | ~ l1_pre_topc(X57)
      | v2_struct_0(X58)
      | ~ v2_pre_topc(X58)
      | ~ l1_pre_topc(X58)
      | ~ m1_pre_topc(X59,X57)
      | ~ m1_pre_topc(X60,X57)
      | ~ v1_funct_1(X61)
      | ~ v1_funct_2(X61,u1_struct_0(X59),u1_struct_0(X58))
      | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X59),u1_struct_0(X58))))
      | ~ m1_pre_topc(X60,X59)
      | k3_tmap_1(X57,X58,X59,X60,X61) = k2_partfun1(u1_struct_0(X59),u1_struct_0(X58),X61,u1_struct_0(X60)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_89,plain,(
    ! [X53,X54,X55,X56] :
      ( v2_struct_0(X53)
      | ~ v2_pre_topc(X53)
      | ~ l1_pre_topc(X53)
      | v2_struct_0(X54)
      | ~ v2_pre_topc(X54)
      | ~ l1_pre_topc(X54)
      | ~ v1_funct_1(X55)
      | ~ v1_funct_2(X55,u1_struct_0(X53),u1_struct_0(X54))
      | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54))))
      | ~ m1_pre_topc(X56,X53)
      | k2_tmap_1(X53,X54,X55,X56) = k2_partfun1(u1_struct_0(X53),u1_struct_0(X54),X55,u1_struct_0(X56)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_90,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_91,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_92,negated_conjecture,
    ( v3_pre_topc(esk3_3(esk5_0,esk10_0,esk9_0),esk7_0)
    | ~ m1_subset_1(esk3_3(esk5_0,esk10_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_39])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(esk3_3(esk5_0,esk10_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_94,plain,
    ( r2_hidden(X1,esk3_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk9_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_69])).

cnf(c_0_96,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_97,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_98,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_99,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_100,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_101,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_39]),c_0_28])])).

cnf(c_0_102,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_103,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_39]),c_0_28]),c_0_29])])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_105,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_106,plain,(
    ! [X71,X72,X73,X74,X75,X76,X77] :
      ( ( ~ r1_tmap_1(X72,X71,X73,X76)
        | r1_tmap_1(X74,X71,k2_tmap_1(X72,X71,X73,X74),X77)
        | ~ r1_tarski(X75,u1_struct_0(X74))
        | ~ m1_connsp_2(X75,X72,X76)
        | X76 != X77
        | ~ m1_subset_1(X77,u1_struct_0(X74))
        | ~ m1_subset_1(X76,u1_struct_0(X72))
        | ~ m1_subset_1(X75,k1_zfmisc_1(u1_struct_0(X72)))
        | v2_struct_0(X74)
        | ~ m1_pre_topc(X74,X72)
        | ~ v1_funct_1(X73)
        | ~ v1_funct_2(X73,u1_struct_0(X72),u1_struct_0(X71))
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X72),u1_struct_0(X71))))
        | v2_struct_0(X72)
        | ~ v2_pre_topc(X72)
        | ~ l1_pre_topc(X72)
        | v2_struct_0(X71)
        | ~ v2_pre_topc(X71)
        | ~ l1_pre_topc(X71) )
      & ( ~ r1_tmap_1(X74,X71,k2_tmap_1(X72,X71,X73,X74),X77)
        | r1_tmap_1(X72,X71,X73,X76)
        | ~ r1_tarski(X75,u1_struct_0(X74))
        | ~ m1_connsp_2(X75,X72,X76)
        | X76 != X77
        | ~ m1_subset_1(X77,u1_struct_0(X74))
        | ~ m1_subset_1(X76,u1_struct_0(X72))
        | ~ m1_subset_1(X75,k1_zfmisc_1(u1_struct_0(X72)))
        | v2_struct_0(X74)
        | ~ m1_pre_topc(X74,X72)
        | ~ v1_funct_1(X73)
        | ~ v1_funct_2(X73,u1_struct_0(X72),u1_struct_0(X71))
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X72),u1_struct_0(X71))))
        | v2_struct_0(X72)
        | ~ v2_pre_topc(X72)
        | ~ l1_pre_topc(X72)
        | v2_struct_0(X71)
        | ~ v2_pre_topc(X71)
        | ~ l1_pre_topc(X71) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tmap_1])])])])])).

cnf(c_0_107,negated_conjecture,
    ( v3_pre_topc(esk3_3(esk5_0,esk10_0,esk9_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_93])])).

cnf(c_0_108,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,esk3_3(X1,X2,X3))
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_94,c_0_45])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(esk9_0,X1)
    | ~ r1_tarski(k1_zfmisc_1(u1_struct_0(esk6_0)),X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_95])).

cnf(c_0_110,plain,
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
    inference(csr,[status(thm)],[c_0_96,c_0_51])).

cnf(c_0_111,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk4_0),esk8_0,u1_struct_0(X1)) = k2_tmap_1(esk7_0,esk4_0,esk8_0,X1)
    | ~ m1_pre_topc(X1,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99]),c_0_100]),c_0_101]),c_0_102]),c_0_103]),c_0_104])]),c_0_105]),c_0_40])).

cnf(c_0_112,plain,
    ( r1_tmap_1(X3,X2,X4,X6)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | ~ r1_tarski(X7,u1_struct_0(X1))
    | ~ m1_connsp_2(X7,X3,X6)
    | X6 != X5
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_113,negated_conjecture,
    ( m1_connsp_2(X1,esk7_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r2_hidden(X2,esk3_3(esk5_0,esk10_0,esk9_0))
    | ~ r1_tarski(esk3_3(esk5_0,esk10_0,esk9_0),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_107]),c_0_101]),c_0_103]),c_0_93])]),c_0_40])).

cnf(c_0_114,negated_conjecture,
    ( r2_hidden(esk10_0,esk3_3(esk5_0,esk10_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_54]),c_0_28]),c_0_29]),c_0_55])]),c_0_31])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(esk9_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_109,c_0_77])).

cnf(c_0_116,negated_conjecture,
    ( k3_tmap_1(X1,esk4_0,esk7_0,X2,esk8_0) = k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk4_0),esk8_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk7_0)
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_98]),c_0_99]),c_0_100]),c_0_102]),c_0_104])]),c_0_105])).

cnf(c_0_117,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk4_0),esk8_0,u1_struct_0(esk6_0)) = k2_tmap_1(esk7_0,esk4_0,esk8_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_111,c_0_62])).

fof(c_0_118,plain,(
    ! [X65,X66,X67,X68,X69,X70] :
      ( v2_struct_0(X65)
      | ~ v2_pre_topc(X65)
      | ~ l1_pre_topc(X65)
      | v2_struct_0(X66)
      | ~ v2_pre_topc(X66)
      | ~ l1_pre_topc(X66)
      | ~ v1_funct_1(X67)
      | ~ v1_funct_2(X67,u1_struct_0(X66),u1_struct_0(X65))
      | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X66),u1_struct_0(X65))))
      | v2_struct_0(X68)
      | ~ m1_pre_topc(X68,X66)
      | ~ m1_subset_1(X69,u1_struct_0(X66))
      | ~ m1_subset_1(X70,u1_struct_0(X68))
      | X69 != X70
      | ~ r1_tmap_1(X66,X65,X67,X69)
      | r1_tmap_1(X68,X65,k2_tmap_1(X66,X65,X67,X68),X70) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).

cnf(c_0_119,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | ~ r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_connsp_2(X6,X1,X4)
    | ~ m1_pre_topc(X5,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ r1_tarski(X6,u1_struct_0(X5)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_112,c_0_45])]),c_0_38])).

cnf(c_0_120,negated_conjecture,
    ( m1_connsp_2(X1,esk7_0,esk10_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r1_tarski(esk3_3(esk5_0,esk10_0,esk9_0),X1) ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_121,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_115])).

cnf(c_0_122,negated_conjecture,
    ( r1_tmap_1(esk7_0,esk4_0,esk8_0,esk10_0)
    | r1_tmap_1(esk6_0,esk4_0,k3_tmap_1(esk5_0,esk4_0,esk7_0,esk6_0,esk8_0),esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_123,negated_conjecture,
    ( esk10_0 = esk11_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_124,negated_conjecture,
    ( k3_tmap_1(X1,esk4_0,esk7_0,esk6_0,esk8_0) = k2_tmap_1(esk7_0,esk4_0,esk8_0,esk6_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_62]),c_0_117])).

cnf(c_0_125,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | X5 != X6
    | ~ r1_tmap_1(X2,X1,X3,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_126,negated_conjecture,
    ( r1_tmap_1(esk7_0,esk4_0,esk8_0,X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X2,esk4_0,k2_tmap_1(esk7_0,esk4_0,esk8_0,X2),X1)
    | ~ m1_connsp_2(X3,esk7_0,X1)
    | ~ m1_pre_topc(X2,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_tarski(X3,u1_struct_0(X2)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_98]),c_0_99]),c_0_101]),c_0_100]),c_0_103]),c_0_102]),c_0_104])]),c_0_105]),c_0_40])).

cnf(c_0_127,negated_conjecture,
    ( m1_connsp_2(esk9_0,esk7_0,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_59]),c_0_121])])).

cnf(c_0_128,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk4_0,k3_tmap_1(esk5_0,esk4_0,esk7_0,esk6_0,esk8_0),esk10_0)
    | r1_tmap_1(esk7_0,esk4_0,esk8_0,esk10_0) ),
    inference(rw,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_129,negated_conjecture,
    ( k3_tmap_1(esk5_0,esk4_0,esk7_0,esk6_0,esk8_0) = k2_tmap_1(esk7_0,esk4_0,esk8_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_39]),c_0_28]),c_0_29])]),c_0_31])).

cnf(c_0_130,negated_conjecture,
    ( m1_subset_1(esk11_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_131,negated_conjecture,
    ( ~ r1_tmap_1(esk7_0,esk4_0,esk8_0,esk10_0)
    | ~ r1_tmap_1(esk6_0,esk4_0,k3_tmap_1(esk5_0,esk4_0,esk7_0,esk6_0,esk8_0),esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_132,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X3,X2,X4,X5)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X4)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_125]),c_0_38])).

cnf(c_0_133,negated_conjecture,
    ( r1_tmap_1(esk7_0,esk4_0,esk8_0,esk10_0)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(X1,esk4_0,k2_tmap_1(esk7_0,esk4_0,esk8_0,X1),esk10_0)
    | ~ m1_pre_topc(X1,esk7_0)
    | ~ m1_subset_1(esk10_0,u1_struct_0(X1))
    | ~ r1_tarski(esk9_0,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_134,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk4_0,k2_tmap_1(esk7_0,esk4_0,esk8_0,esk6_0),esk10_0)
    | r1_tmap_1(esk7_0,esk4_0,esk8_0,esk10_0) ),
    inference(rw,[status(thm)],[c_0_128,c_0_129])).

cnf(c_0_135,negated_conjecture,
    ( m1_subset_1(esk10_0,u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_130,c_0_123])).

cnf(c_0_136,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_137,negated_conjecture,
    ( ~ r1_tmap_1(esk6_0,esk4_0,k3_tmap_1(esk5_0,esk4_0,esk7_0,esk6_0,esk8_0),esk10_0)
    | ~ r1_tmap_1(esk7_0,esk4_0,esk8_0,esk10_0) ),
    inference(rw,[status(thm)],[c_0_131,c_0_123])).

cnf(c_0_138,negated_conjecture,
    ( r1_tmap_1(X1,esk4_0,k2_tmap_1(esk7_0,esk4_0,esk8_0,X1),X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk7_0,esk4_0,esk8_0,X2)
    | ~ m1_pre_topc(X1,esk7_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_98]),c_0_99]),c_0_101]),c_0_100]),c_0_103]),c_0_102]),c_0_104])]),c_0_105]),c_0_40])).

cnf(c_0_139,negated_conjecture,
    ( r1_tmap_1(esk7_0,esk4_0,esk8_0,esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_134]),c_0_62]),c_0_135]),c_0_69])]),c_0_136])).

cnf(c_0_140,negated_conjecture,
    ( ~ r1_tmap_1(esk6_0,esk4_0,k2_tmap_1(esk7_0,esk4_0,esk8_0,esk6_0),esk10_0)
    | ~ r1_tmap_1(esk7_0,esk4_0,esk8_0,esk10_0) ),
    inference(rw,[status(thm)],[c_0_137,c_0_129])).

cnf(c_0_141,negated_conjecture,
    ( r1_tmap_1(X1,esk4_0,k2_tmap_1(esk7_0,esk4_0,esk8_0,X1),esk10_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk7_0)
    | ~ m1_subset_1(esk10_0,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_138,c_0_139])).

cnf(c_0_142,negated_conjecture,
    ( ~ r1_tmap_1(esk6_0,esk4_0,k2_tmap_1(esk7_0,esk4_0,esk8_0,esk6_0),esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_140,c_0_139])])).

cnf(c_0_143,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_62]),c_0_135])]),c_0_142]),c_0_136]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.57  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.20/0.57  # and selection function SelectCQIPrecWNTNp.
% 0.20/0.57  #
% 0.20/0.57  # Preprocessing time       : 0.031 s
% 0.20/0.57  # Presaturation interreduction done
% 0.20/0.57  
% 0.20/0.57  # Proof found!
% 0.20/0.57  # SZS status Theorem
% 0.20/0.57  # SZS output start CNFRefutation
% 0.20/0.57  fof(t8_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 0.20/0.57  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.57  fof(t85_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X2)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X1,X5,X7)<=>r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,X4,X3,X5),X8)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_tmap_1)).
% 0.20/0.57  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.57  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.20/0.57  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.20/0.57  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.20/0.57  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.20/0.57  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.57  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.57  fof(t79_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 0.20/0.57  fof(t33_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v3_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v3_pre_topc(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 0.20/0.57  fof(t39_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.20/0.57  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.57  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.57  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.20/0.57  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.20/0.57  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.20/0.57  fof(t65_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>(((r1_tarski(X5,u1_struct_0(X4))&m1_connsp_2(X5,X2,X6))&X6=X7)=>(r1_tmap_1(X2,X1,X3,X6)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X7)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 0.20/0.57  fof(t64_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>((X5=X6&r1_tmap_1(X2,X1,X3,X5))=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 0.20/0.57  fof(c_0_20, plain, ![X48, X49, X50, X52]:(((((m1_subset_1(esk3_3(X48,X49,X50),k1_zfmisc_1(u1_struct_0(X48)))|~m1_connsp_2(X50,X48,X49)|~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X48)))|~m1_subset_1(X49,u1_struct_0(X48))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)))&(v3_pre_topc(esk3_3(X48,X49,X50),X48)|~m1_connsp_2(X50,X48,X49)|~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X48)))|~m1_subset_1(X49,u1_struct_0(X48))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48))))&(r1_tarski(esk3_3(X48,X49,X50),X50)|~m1_connsp_2(X50,X48,X49)|~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X48)))|~m1_subset_1(X49,u1_struct_0(X48))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48))))&(r2_hidden(X49,esk3_3(X48,X49,X50))|~m1_connsp_2(X50,X48,X49)|~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X48)))|~m1_subset_1(X49,u1_struct_0(X48))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48))))&(~m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X48)))|~v3_pre_topc(X52,X48)|~r1_tarski(X52,X50)|~r2_hidden(X49,X52)|m1_connsp_2(X50,X48,X49)|~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X48)))|~m1_subset_1(X49,u1_struct_0(X48))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_connsp_2])])])])])])).
% 0.20/0.57  fof(c_0_21, plain, ![X28, X29, X30]:(~r2_hidden(X28,X29)|~m1_subset_1(X29,k1_zfmisc_1(X30))|m1_subset_1(X28,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.57  fof(c_0_22, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X2)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X1,X5,X7)<=>r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,X4,X3,X5),X8))))))))))))), inference(assume_negation,[status(cth)],[t85_tmap_1])).
% 0.20/0.57  cnf(c_0_23, plain, (m1_connsp_2(X3,X2,X4)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|~r1_tarski(X1,X3)|~r2_hidden(X4,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.57  cnf(c_0_24, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.57  fof(c_0_25, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&((~v2_struct_0(esk6_0)&m1_pre_topc(esk6_0,esk5_0))&((~v2_struct_0(esk7_0)&m1_pre_topc(esk7_0,esk5_0))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk4_0)))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk4_0)))))&(m1_pre_topc(esk6_0,esk7_0)&(m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&(m1_subset_1(esk10_0,u1_struct_0(esk7_0))&(m1_subset_1(esk11_0,u1_struct_0(esk6_0))&((((v3_pre_topc(esk9_0,esk5_0)&r2_hidden(esk10_0,esk9_0))&r1_tarski(esk9_0,u1_struct_0(esk6_0)))&esk10_0=esk11_0)&((~r1_tmap_1(esk7_0,esk4_0,esk8_0,esk10_0)|~r1_tmap_1(esk6_0,esk4_0,k3_tmap_1(esk5_0,esk4_0,esk7_0,esk6_0,esk8_0),esk11_0))&(r1_tmap_1(esk7_0,esk4_0,esk8_0,esk10_0)|r1_tmap_1(esk6_0,esk4_0,k3_tmap_1(esk5_0,esk4_0,esk7_0,esk6_0,esk8_0),esk11_0))))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).
% 0.20/0.57  cnf(c_0_26, plain, (m1_connsp_2(X1,X2,X3)|v2_struct_0(X2)|~v3_pre_topc(X4,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X4)|~r1_tarski(X4,X1)), inference(csr,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.57  cnf(c_0_27, negated_conjecture, (v3_pre_topc(esk9_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  cnf(c_0_29, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  fof(c_0_32, plain, ![X15, X16]:(((r1_tarski(X15,X16)|X15!=X16)&(r1_tarski(X16,X15)|X15!=X16))&(~r1_tarski(X15,X16)|~r1_tarski(X16,X15)|X15=X16)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.57  fof(c_0_33, plain, ![X38, X39, X40]:(v2_struct_0(X38)|~l1_pre_topc(X38)|(v2_struct_0(X39)|~m1_pre_topc(X39,X38)|(~m1_subset_1(X40,u1_struct_0(X39))|m1_subset_1(X40,u1_struct_0(X38))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.20/0.57  fof(c_0_34, plain, ![X45, X46, X47]:(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)|~m1_subset_1(X46,u1_struct_0(X45))|(~m1_connsp_2(X47,X45,X46)|m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.20/0.57  cnf(c_0_35, negated_conjecture, (m1_connsp_2(X1,esk5_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r2_hidden(X2,esk9_0)|~r1_tarski(esk9_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30])]), c_0_31])).
% 0.20/0.57  cnf(c_0_36, negated_conjecture, (r2_hidden(esk10_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  cnf(c_0_37, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.57  cnf(c_0_38, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.57  cnf(c_0_39, negated_conjecture, (m1_pre_topc(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  cnf(c_0_40, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  fof(c_0_41, plain, ![X62, X63, X64]:((~r1_tarski(u1_struct_0(X63),u1_struct_0(X64))|m1_pre_topc(X63,X64)|~m1_pre_topc(X64,X62)|~m1_pre_topc(X63,X62)|(~v2_pre_topc(X62)|~l1_pre_topc(X62)))&(~m1_pre_topc(X63,X64)|r1_tarski(u1_struct_0(X63),u1_struct_0(X64))|~m1_pre_topc(X64,X62)|~m1_pre_topc(X63,X62)|(~v2_pre_topc(X62)|~l1_pre_topc(X62)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.20/0.57  fof(c_0_42, plain, ![X78, X79, X80]:(~v2_pre_topc(X78)|~l1_pre_topc(X78)|(~m1_pre_topc(X79,X78)|(~m1_pre_topc(X80,X79)|m1_pre_topc(X80,X78)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.20/0.57  fof(c_0_43, plain, ![X17, X18, X19, X20, X21, X22]:(((~r2_hidden(X19,X18)|r1_tarski(X19,X17)|X18!=k1_zfmisc_1(X17))&(~r1_tarski(X20,X17)|r2_hidden(X20,X18)|X18!=k1_zfmisc_1(X17)))&((~r2_hidden(esk2_2(X21,X22),X22)|~r1_tarski(esk2_2(X21,X22),X21)|X22=k1_zfmisc_1(X21))&(r2_hidden(esk2_2(X21,X22),X22)|r1_tarski(esk2_2(X21,X22),X21)|X22=k1_zfmisc_1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.57  cnf(c_0_44, plain, (r1_tarski(esk3_3(X1,X2,X3),X3)|v2_struct_0(X1)|~m1_connsp_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.57  cnf(c_0_45, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.57  cnf(c_0_46, negated_conjecture, (m1_connsp_2(X1,esk5_0,esk10_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(esk9_0,X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.57  cnf(c_0_47, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_37])).
% 0.20/0.57  cnf(c_0_48, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_28])]), c_0_40]), c_0_31])).
% 0.20/0.57  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk10_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  cnf(c_0_50, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.57  cnf(c_0_51, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.57  cnf(c_0_52, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.57  cnf(c_0_53, plain, (v2_struct_0(X1)|r1_tarski(esk3_3(X1,X2,X3),X3)|~m1_connsp_2(X3,X1,X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.57  cnf(c_0_54, negated_conjecture, (m1_connsp_2(esk9_0,esk5_0,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_30])])).
% 0.20/0.57  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk10_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.57  cnf(c_0_56, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X3)|~v2_pre_topc(X3)), inference(csr,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.57  fof(c_0_57, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk1_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk1_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.57  cnf(c_0_58, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_52])).
% 0.20/0.57  cnf(c_0_59, negated_conjecture, (r1_tarski(esk3_3(esk5_0,esk10_0,esk9_0),esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_28]), c_0_29]), c_0_55])]), c_0_31])).
% 0.20/0.57  fof(c_0_60, plain, ![X24, X25]:(~r1_tarski(X24,X25)|r1_tarski(k1_zfmisc_1(X24),k1_zfmisc_1(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).
% 0.20/0.57  cnf(c_0_61, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk7_0))|~m1_pre_topc(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_39]), c_0_28]), c_0_29])])).
% 0.20/0.57  cnf(c_0_62, negated_conjecture, (m1_pre_topc(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  fof(c_0_63, plain, ![X41, X42, X43, X44]:(~l1_pre_topc(X41)|(~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|(~m1_pre_topc(X43,X41)|(~v3_pre_topc(X42,X41)|(~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))|(X44!=X42|v3_pre_topc(X44,X43))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_tops_2])])])).
% 0.20/0.57  fof(c_0_64, plain, ![X35, X36, X37]:(~l1_pre_topc(X35)|(~m1_pre_topc(X36,X35)|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).
% 0.20/0.57  cnf(c_0_65, plain, (v3_pre_topc(esk3_3(X1,X2,X3),X1)|v2_struct_0(X1)|~m1_connsp_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.57  cnf(c_0_66, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.57  cnf(c_0_67, negated_conjecture, (r2_hidden(esk3_3(esk5_0,esk10_0,esk9_0),k1_zfmisc_1(esk9_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.57  cnf(c_0_68, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.57  cnf(c_0_69, negated_conjecture, (r1_tarski(esk9_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  cnf(c_0_70, negated_conjecture, (r1_tarski(u1_struct_0(esk6_0),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.57  cnf(c_0_71, plain, (v3_pre_topc(X4,X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X3,X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|X4!=X2), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.57  cnf(c_0_72, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.57  cnf(c_0_73, plain, (v3_pre_topc(esk3_3(X1,X2,X3),X1)|v2_struct_0(X1)|~m1_connsp_2(X3,X1,X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_65, c_0_45])).
% 0.20/0.57  cnf(c_0_74, negated_conjecture, (r2_hidden(esk3_3(esk5_0,esk10_0,esk9_0),X1)|~r1_tarski(k1_zfmisc_1(esk9_0),X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.57  cnf(c_0_75, negated_conjecture, (r1_tarski(k1_zfmisc_1(esk9_0),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.57  fof(c_0_76, plain, ![X26, X27]:(~r2_hidden(X26,X27)|m1_subset_1(X26,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.57  cnf(c_0_77, negated_conjecture, (r1_tarski(k1_zfmisc_1(u1_struct_0(esk6_0)),k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(spm,[status(thm)],[c_0_68, c_0_70])).
% 0.20/0.57  cnf(c_0_78, plain, (v3_pre_topc(X1,X2)|~v3_pre_topc(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_71]), c_0_72])).
% 0.20/0.57  cnf(c_0_79, negated_conjecture, (v3_pre_topc(esk3_3(esk5_0,esk10_0,esk9_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_54]), c_0_28]), c_0_29]), c_0_55])]), c_0_31])).
% 0.20/0.57  cnf(c_0_80, negated_conjecture, (r2_hidden(esk3_3(esk5_0,esk10_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.57  cnf(c_0_81, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.57  cnf(c_0_82, negated_conjecture, (r2_hidden(k1_zfmisc_1(u1_struct_0(esk6_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))), inference(spm,[status(thm)],[c_0_58, c_0_77])).
% 0.20/0.57  fof(c_0_83, plain, ![X33, X34]:(~l1_pre_topc(X33)|(~m1_pre_topc(X34,X33)|l1_pre_topc(X34))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.57  fof(c_0_84, plain, ![X31, X32]:(~v2_pre_topc(X31)|~l1_pre_topc(X31)|(~m1_pre_topc(X32,X31)|v2_pre_topc(X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.20/0.57  cnf(c_0_85, negated_conjecture, (v3_pre_topc(esk3_3(esk5_0,esk10_0,esk9_0),X1)|~m1_pre_topc(X1,esk5_0)|~m1_subset_1(esk3_3(esk5_0,esk10_0,esk9_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_28])])).
% 0.20/0.57  cnf(c_0_86, negated_conjecture, (m1_subset_1(esk3_3(esk5_0,esk10_0,esk9_0),X1)|~m1_subset_1(k1_zfmisc_1(u1_struct_0(esk6_0)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_24, c_0_80])).
% 0.20/0.57  cnf(c_0_87, negated_conjecture, (m1_subset_1(k1_zfmisc_1(u1_struct_0(esk6_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.20/0.57  fof(c_0_88, plain, ![X57, X58, X59, X60, X61]:(v2_struct_0(X57)|~v2_pre_topc(X57)|~l1_pre_topc(X57)|(v2_struct_0(X58)|~v2_pre_topc(X58)|~l1_pre_topc(X58)|(~m1_pre_topc(X59,X57)|(~m1_pre_topc(X60,X57)|(~v1_funct_1(X61)|~v1_funct_2(X61,u1_struct_0(X59),u1_struct_0(X58))|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X59),u1_struct_0(X58))))|(~m1_pre_topc(X60,X59)|k3_tmap_1(X57,X58,X59,X60,X61)=k2_partfun1(u1_struct_0(X59),u1_struct_0(X58),X61,u1_struct_0(X60)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.20/0.57  fof(c_0_89, plain, ![X53, X54, X55, X56]:(v2_struct_0(X53)|~v2_pre_topc(X53)|~l1_pre_topc(X53)|(v2_struct_0(X54)|~v2_pre_topc(X54)|~l1_pre_topc(X54)|(~v1_funct_1(X55)|~v1_funct_2(X55,u1_struct_0(X53),u1_struct_0(X54))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54))))|(~m1_pre_topc(X56,X53)|k2_tmap_1(X53,X54,X55,X56)=k2_partfun1(u1_struct_0(X53),u1_struct_0(X54),X55,u1_struct_0(X56)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.20/0.57  cnf(c_0_90, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.20/0.57  cnf(c_0_91, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.20/0.57  cnf(c_0_92, negated_conjecture, (v3_pre_topc(esk3_3(esk5_0,esk10_0,esk9_0),esk7_0)|~m1_subset_1(esk3_3(esk5_0,esk10_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(spm,[status(thm)],[c_0_85, c_0_39])).
% 0.20/0.57  cnf(c_0_93, negated_conjecture, (m1_subset_1(esk3_3(esk5_0,esk10_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.20/0.57  cnf(c_0_94, plain, (r2_hidden(X1,esk3_3(X2,X1,X3))|v2_struct_0(X2)|~m1_connsp_2(X3,X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.57  cnf(c_0_95, negated_conjecture, (r2_hidden(esk9_0,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_58, c_0_69])).
% 0.20/0.57  cnf(c_0_96, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.20/0.57  cnf(c_0_97, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.20/0.57  cnf(c_0_98, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  cnf(c_0_99, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  cnf(c_0_100, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  cnf(c_0_101, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_39]), c_0_28])])).
% 0.20/0.57  cnf(c_0_102, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  cnf(c_0_103, negated_conjecture, (v2_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_39]), c_0_28]), c_0_29])])).
% 0.20/0.57  cnf(c_0_104, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  cnf(c_0_105, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  fof(c_0_106, plain, ![X71, X72, X73, X74, X75, X76, X77]:((~r1_tmap_1(X72,X71,X73,X76)|r1_tmap_1(X74,X71,k2_tmap_1(X72,X71,X73,X74),X77)|(~r1_tarski(X75,u1_struct_0(X74))|~m1_connsp_2(X75,X72,X76)|X76!=X77)|~m1_subset_1(X77,u1_struct_0(X74))|~m1_subset_1(X76,u1_struct_0(X72))|~m1_subset_1(X75,k1_zfmisc_1(u1_struct_0(X72)))|(v2_struct_0(X74)|~m1_pre_topc(X74,X72))|(~v1_funct_1(X73)|~v1_funct_2(X73,u1_struct_0(X72),u1_struct_0(X71))|~m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X72),u1_struct_0(X71)))))|(v2_struct_0(X72)|~v2_pre_topc(X72)|~l1_pre_topc(X72))|(v2_struct_0(X71)|~v2_pre_topc(X71)|~l1_pre_topc(X71)))&(~r1_tmap_1(X74,X71,k2_tmap_1(X72,X71,X73,X74),X77)|r1_tmap_1(X72,X71,X73,X76)|(~r1_tarski(X75,u1_struct_0(X74))|~m1_connsp_2(X75,X72,X76)|X76!=X77)|~m1_subset_1(X77,u1_struct_0(X74))|~m1_subset_1(X76,u1_struct_0(X72))|~m1_subset_1(X75,k1_zfmisc_1(u1_struct_0(X72)))|(v2_struct_0(X74)|~m1_pre_topc(X74,X72))|(~v1_funct_1(X73)|~v1_funct_2(X73,u1_struct_0(X72),u1_struct_0(X71))|~m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X72),u1_struct_0(X71)))))|(v2_struct_0(X72)|~v2_pre_topc(X72)|~l1_pre_topc(X72))|(v2_struct_0(X71)|~v2_pre_topc(X71)|~l1_pre_topc(X71)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tmap_1])])])])])).
% 0.20/0.57  cnf(c_0_107, negated_conjecture, (v3_pre_topc(esk3_3(esk5_0,esk10_0,esk9_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_93])])).
% 0.20/0.57  cnf(c_0_108, plain, (v2_struct_0(X1)|r2_hidden(X2,esk3_3(X1,X2,X3))|~m1_connsp_2(X3,X1,X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_94, c_0_45])).
% 0.20/0.57  cnf(c_0_109, negated_conjecture, (r2_hidden(esk9_0,X1)|~r1_tarski(k1_zfmisc_1(u1_struct_0(esk6_0)),X1)), inference(spm,[status(thm)],[c_0_66, c_0_95])).
% 0.20/0.57  cnf(c_0_110, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(csr,[status(thm)],[c_0_96, c_0_51])).
% 0.20/0.57  cnf(c_0_111, negated_conjecture, (k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk4_0),esk8_0,u1_struct_0(X1))=k2_tmap_1(esk7_0,esk4_0,esk8_0,X1)|~m1_pre_topc(X1,esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99]), c_0_100]), c_0_101]), c_0_102]), c_0_103]), c_0_104])]), c_0_105]), c_0_40])).
% 0.20/0.57  cnf(c_0_112, plain, (r1_tmap_1(X3,X2,X4,X6)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|~r1_tarski(X7,u1_struct_0(X1))|~m1_connsp_2(X7,X3,X6)|X6!=X5|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_106])).
% 0.20/0.57  cnf(c_0_113, negated_conjecture, (m1_connsp_2(X1,esk7_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))|~r2_hidden(X2,esk3_3(esk5_0,esk10_0,esk9_0))|~r1_tarski(esk3_3(esk5_0,esk10_0,esk9_0),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_107]), c_0_101]), c_0_103]), c_0_93])]), c_0_40])).
% 0.20/0.57  cnf(c_0_114, negated_conjecture, (r2_hidden(esk10_0,esk3_3(esk5_0,esk10_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_54]), c_0_28]), c_0_29]), c_0_55])]), c_0_31])).
% 0.20/0.57  cnf(c_0_115, negated_conjecture, (r2_hidden(esk9_0,k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(spm,[status(thm)],[c_0_109, c_0_77])).
% 0.20/0.57  cnf(c_0_116, negated_conjecture, (k3_tmap_1(X1,esk4_0,esk7_0,X2,esk8_0)=k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk4_0),esk8_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk7_0)|~m1_pre_topc(esk7_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_98]), c_0_99]), c_0_100]), c_0_102]), c_0_104])]), c_0_105])).
% 0.20/0.57  cnf(c_0_117, negated_conjecture, (k2_partfun1(u1_struct_0(esk7_0),u1_struct_0(esk4_0),esk8_0,u1_struct_0(esk6_0))=k2_tmap_1(esk7_0,esk4_0,esk8_0,esk6_0)), inference(spm,[status(thm)],[c_0_111, c_0_62])).
% 0.20/0.57  fof(c_0_118, plain, ![X65, X66, X67, X68, X69, X70]:(v2_struct_0(X65)|~v2_pre_topc(X65)|~l1_pre_topc(X65)|(v2_struct_0(X66)|~v2_pre_topc(X66)|~l1_pre_topc(X66)|(~v1_funct_1(X67)|~v1_funct_2(X67,u1_struct_0(X66),u1_struct_0(X65))|~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X66),u1_struct_0(X65))))|(v2_struct_0(X68)|~m1_pre_topc(X68,X66)|(~m1_subset_1(X69,u1_struct_0(X66))|(~m1_subset_1(X70,u1_struct_0(X68))|(X69!=X70|~r1_tmap_1(X66,X65,X67,X69)|r1_tmap_1(X68,X65,k2_tmap_1(X66,X65,X67,X68),X70)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).
% 0.20/0.57  cnf(c_0_119, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X5)|~r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~m1_connsp_2(X6,X1,X4)|~m1_pre_topc(X5,X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~v2_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,u1_struct_0(X5))|~r1_tarski(X6,u1_struct_0(X5))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_112, c_0_45])]), c_0_38])).
% 0.20/0.57  cnf(c_0_120, negated_conjecture, (m1_connsp_2(X1,esk7_0,esk10_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))|~r1_tarski(esk3_3(esk5_0,esk10_0,esk9_0),X1)), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 0.20/0.57  cnf(c_0_121, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(spm,[status(thm)],[c_0_81, c_0_115])).
% 0.20/0.57  cnf(c_0_122, negated_conjecture, (r1_tmap_1(esk7_0,esk4_0,esk8_0,esk10_0)|r1_tmap_1(esk6_0,esk4_0,k3_tmap_1(esk5_0,esk4_0,esk7_0,esk6_0,esk8_0),esk11_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  cnf(c_0_123, negated_conjecture, (esk10_0=esk11_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  cnf(c_0_124, negated_conjecture, (k3_tmap_1(X1,esk4_0,esk7_0,esk6_0,esk8_0)=k2_tmap_1(esk7_0,esk4_0,esk8_0,esk6_0)|v2_struct_0(X1)|~m1_pre_topc(esk7_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_62]), c_0_117])).
% 0.20/0.57  cnf(c_0_125, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X4)|r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X4,X2)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X6,u1_struct_0(X4))|X5!=X6|~r1_tmap_1(X2,X1,X3,X5)), inference(split_conjunct,[status(thm)],[c_0_118])).
% 0.20/0.57  cnf(c_0_126, negated_conjecture, (r1_tmap_1(esk7_0,esk4_0,esk8_0,X1)|v2_struct_0(X2)|~r1_tmap_1(X2,esk4_0,k2_tmap_1(esk7_0,esk4_0,esk8_0,X2),X1)|~m1_connsp_2(X3,esk7_0,X1)|~m1_pre_topc(X2,esk7_0)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_tarski(X3,u1_struct_0(X2))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_98]), c_0_99]), c_0_101]), c_0_100]), c_0_103]), c_0_102]), c_0_104])]), c_0_105]), c_0_40])).
% 0.20/0.57  cnf(c_0_127, negated_conjecture, (m1_connsp_2(esk9_0,esk7_0,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_59]), c_0_121])])).
% 0.20/0.57  cnf(c_0_128, negated_conjecture, (r1_tmap_1(esk6_0,esk4_0,k3_tmap_1(esk5_0,esk4_0,esk7_0,esk6_0,esk8_0),esk10_0)|r1_tmap_1(esk7_0,esk4_0,esk8_0,esk10_0)), inference(rw,[status(thm)],[c_0_122, c_0_123])).
% 0.20/0.57  cnf(c_0_129, negated_conjecture, (k3_tmap_1(esk5_0,esk4_0,esk7_0,esk6_0,esk8_0)=k2_tmap_1(esk7_0,esk4_0,esk8_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_39]), c_0_28]), c_0_29])]), c_0_31])).
% 0.20/0.57  cnf(c_0_130, negated_conjecture, (m1_subset_1(esk11_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  cnf(c_0_131, negated_conjecture, (~r1_tmap_1(esk7_0,esk4_0,esk8_0,esk10_0)|~r1_tmap_1(esk6_0,esk4_0,k3_tmap_1(esk5_0,esk4_0,esk7_0,esk6_0,esk8_0),esk11_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  cnf(c_0_132, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X3,X2,X4,X5)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X4)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X5,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_125]), c_0_38])).
% 0.20/0.57  cnf(c_0_133, negated_conjecture, (r1_tmap_1(esk7_0,esk4_0,esk8_0,esk10_0)|v2_struct_0(X1)|~r1_tmap_1(X1,esk4_0,k2_tmap_1(esk7_0,esk4_0,esk8_0,X1),esk10_0)|~m1_pre_topc(X1,esk7_0)|~m1_subset_1(esk10_0,u1_struct_0(X1))|~r1_tarski(esk9_0,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 0.20/0.57  cnf(c_0_134, negated_conjecture, (r1_tmap_1(esk6_0,esk4_0,k2_tmap_1(esk7_0,esk4_0,esk8_0,esk6_0),esk10_0)|r1_tmap_1(esk7_0,esk4_0,esk8_0,esk10_0)), inference(rw,[status(thm)],[c_0_128, c_0_129])).
% 0.20/0.57  cnf(c_0_135, negated_conjecture, (m1_subset_1(esk10_0,u1_struct_0(esk6_0))), inference(rw,[status(thm)],[c_0_130, c_0_123])).
% 0.20/0.57  cnf(c_0_136, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.57  cnf(c_0_137, negated_conjecture, (~r1_tmap_1(esk6_0,esk4_0,k3_tmap_1(esk5_0,esk4_0,esk7_0,esk6_0,esk8_0),esk10_0)|~r1_tmap_1(esk7_0,esk4_0,esk8_0,esk10_0)), inference(rw,[status(thm)],[c_0_131, c_0_123])).
% 0.20/0.57  cnf(c_0_138, negated_conjecture, (r1_tmap_1(X1,esk4_0,k2_tmap_1(esk7_0,esk4_0,esk8_0,X1),X2)|v2_struct_0(X1)|~r1_tmap_1(esk7_0,esk4_0,esk8_0,X2)|~m1_pre_topc(X1,esk7_0)|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_98]), c_0_99]), c_0_101]), c_0_100]), c_0_103]), c_0_102]), c_0_104])]), c_0_105]), c_0_40])).
% 0.20/0.57  cnf(c_0_139, negated_conjecture, (r1_tmap_1(esk7_0,esk4_0,esk8_0,esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_134]), c_0_62]), c_0_135]), c_0_69])]), c_0_136])).
% 0.20/0.57  cnf(c_0_140, negated_conjecture, (~r1_tmap_1(esk6_0,esk4_0,k2_tmap_1(esk7_0,esk4_0,esk8_0,esk6_0),esk10_0)|~r1_tmap_1(esk7_0,esk4_0,esk8_0,esk10_0)), inference(rw,[status(thm)],[c_0_137, c_0_129])).
% 0.20/0.57  cnf(c_0_141, negated_conjecture, (r1_tmap_1(X1,esk4_0,k2_tmap_1(esk7_0,esk4_0,esk8_0,X1),esk10_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk7_0)|~m1_subset_1(esk10_0,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_138, c_0_139])).
% 0.20/0.57  cnf(c_0_142, negated_conjecture, (~r1_tmap_1(esk6_0,esk4_0,k2_tmap_1(esk7_0,esk4_0,esk8_0,esk6_0),esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_140, c_0_139])])).
% 0.20/0.57  cnf(c_0_143, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_62]), c_0_135])]), c_0_142]), c_0_136]), ['proof']).
% 0.20/0.57  # SZS output end CNFRefutation
% 0.20/0.57  # Proof object total steps             : 144
% 0.20/0.57  # Proof object clause steps            : 103
% 0.20/0.57  # Proof object formula steps           : 41
% 0.20/0.57  # Proof object conjectures             : 73
% 0.20/0.57  # Proof object clause conjectures      : 70
% 0.20/0.57  # Proof object formula conjectures     : 3
% 0.20/0.57  # Proof object initial clauses used    : 44
% 0.20/0.57  # Proof object initial formulas used   : 20
% 0.20/0.57  # Proof object generating inferences   : 41
% 0.20/0.57  # Proof object simplifying inferences  : 114
% 0.20/0.57  # Training examples: 0 positive, 0 negative
% 0.20/0.57  # Parsed axioms                        : 20
% 0.20/0.57  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.57  # Initial clauses                      : 55
% 0.20/0.57  # Removed in clause preprocessing      : 0
% 0.20/0.57  # Initial clauses in saturation        : 55
% 0.20/0.57  # Processed clauses                    : 2318
% 0.20/0.57  # ...of these trivial                  : 243
% 0.20/0.57  # ...subsumed                          : 158
% 0.20/0.57  # ...remaining for further processing  : 1917
% 0.20/0.57  # Other redundant clauses eliminated   : 8
% 0.20/0.57  # Clauses deleted for lack of memory   : 0
% 0.20/0.57  # Backward-subsumed                    : 0
% 0.20/0.57  # Backward-rewritten                   : 9
% 0.20/0.57  # Generated clauses                    : 5658
% 0.20/0.57  # ...of the previous two non-trivial   : 4375
% 0.20/0.57  # Contextual simplify-reflections      : 47
% 0.20/0.57  # Paramodulations                      : 5648
% 0.20/0.57  # Factorizations                       : 2
% 0.20/0.57  # Equation resolutions                 : 8
% 0.20/0.57  # Propositional unsat checks           : 0
% 0.20/0.57  #    Propositional check models        : 0
% 0.20/0.57  #    Propositional check unsatisfiable : 0
% 0.20/0.57  #    Propositional clauses             : 0
% 0.20/0.57  #    Propositional clauses after purity: 0
% 0.20/0.57  #    Propositional unsat core size     : 0
% 0.20/0.57  #    Propositional preprocessing time  : 0.000
% 0.20/0.57  #    Propositional encoding time       : 0.000
% 0.20/0.57  #    Propositional solver time         : 0.000
% 0.20/0.57  #    Success case prop preproc time    : 0.000
% 0.20/0.57  #    Success case prop encoding time   : 0.000
% 0.20/0.57  #    Success case prop solver time     : 0.000
% 0.20/0.57  # Current number of processed clauses  : 1847
% 0.20/0.57  #    Positive orientable unit clauses  : 863
% 0.20/0.57  #    Positive unorientable unit clauses: 0
% 0.20/0.57  #    Negative unit clauses             : 5
% 0.20/0.57  #    Non-unit-clauses                  : 979
% 0.20/0.57  # Current number of unprocessed clauses: 2164
% 0.20/0.57  # ...number of literals in the above   : 6509
% 0.20/0.57  # Current number of archived formulas  : 0
% 0.20/0.57  # Current number of archived clauses   : 62
% 0.20/0.57  # Clause-clause subsumption calls (NU) : 32273
% 0.20/0.57  # Rec. Clause-clause subsumption calls : 23410
% 0.20/0.57  # Non-unit clause-clause subsumptions  : 205
% 0.20/0.57  # Unit Clause-clause subsumption calls : 4649
% 0.20/0.57  # Rewrite failures with RHS unbound    : 0
% 0.20/0.57  # BW rewrite match attempts            : 41440
% 0.20/0.57  # BW rewrite match successes           : 6
% 0.20/0.57  # Condensation attempts                : 0
% 0.20/0.57  # Condensation successes               : 0
% 0.20/0.57  # Termbank termtop insertions          : 145121
% 0.20/0.57  
% 0.20/0.57  # -------------------------------------------------
% 0.20/0.57  # User time                : 0.221 s
% 0.20/0.57  # System time              : 0.011 s
% 0.20/0.57  # Total time               : 0.232 s
% 0.20/0.57  # Maximum resident set size: 1620 pages
%------------------------------------------------------------------------------
