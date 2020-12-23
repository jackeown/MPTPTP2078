%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:48 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 967 expanded)
%              Number of clauses        :   68 ( 329 expanded)
%              Number of leaves         :   16 ( 233 expanded)
%              Depth                    :   13
%              Number of atoms          :  609 (13793 expanded)
%              Number of equality atoms :   31 ( 585 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

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

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,X18)
      | l1_pre_topc(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk3_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    & m1_pre_topc(esk4_0,esk5_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk8_0,u1_struct_0(esk5_0))
    & m1_subset_1(esk9_0,u1_struct_0(esk4_0))
    & v3_pre_topc(esk7_0,esk3_0)
    & r2_hidden(esk8_0,esk7_0)
    & r1_tarski(esk7_0,u1_struct_0(esk4_0))
    & esk8_0 = esk9_0
    & ( ~ r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)
      | ~ r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk9_0) )
    & ( r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)
      | r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_19,plain,(
    ! [X26,X27,X28,X29] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ m1_pre_topc(X28,X26)
      | ~ v3_pre_topc(X27,X26)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | X29 != X27
      | v3_pre_topc(X29,X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_tops_2])])])).

fof(c_0_20,plain,(
    ! [X20,X21,X22] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_pre_topc(X21,X20)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

cnf(c_0_21,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_25,plain,(
    ! [X16,X17] :
      ( ~ v2_pre_topc(X16)
      | ~ l1_pre_topc(X16)
      | ~ m1_pre_topc(X17,X16)
      | v2_pre_topc(X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_26,plain,(
    ! [X33,X34,X35,X37] :
      ( ( m1_subset_1(esk1_3(X33,X34,X35),k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_connsp_2(X35,X33,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( v3_pre_topc(esk1_3(X33,X34,X35),X33)
        | ~ m1_connsp_2(X35,X33,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( r1_tarski(esk1_3(X33,X34,X35),X35)
        | ~ m1_connsp_2(X35,X33,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( r2_hidden(X34,esk1_3(X33,X34,X35))
        | ~ m1_connsp_2(X35,X33,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ v3_pre_topc(X37,X33)
        | ~ r1_tarski(X37,X35)
        | ~ r2_hidden(X34,X37)
        | m1_connsp_2(X35,X33,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_connsp_2])])])])])])).

fof(c_0_27,plain,(
    ! [X13,X14,X15] :
      ( ~ r2_hidden(X13,X14)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X15))
      | m1_subset_1(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_28,plain,
    ( v3_pre_topc(X4,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | X4 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_34,plain,(
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

fof(c_0_35,plain,(
    ! [X60,X61,X62] :
      ( ~ v2_pre_topc(X60)
      | ~ l1_pre_topc(X60)
      | ~ m1_pre_topc(X61,X60)
      | ~ m1_pre_topc(X62,X61)
      | m1_pre_topc(X62,X60) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_36,plain,(
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

cnf(c_0_37,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v3_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_45,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_50,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_51,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_52,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_22]),c_0_23]),c_0_38])])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_54,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_55,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_56,plain,(
    ! [X53,X54,X55,X56,X57,X58,X59] :
      ( ( ~ r1_tmap_1(X54,X53,X55,X58)
        | r1_tmap_1(X56,X53,k2_tmap_1(X54,X53,X55,X56),X59)
        | ~ r1_tarski(X57,u1_struct_0(X56))
        | ~ m1_connsp_2(X57,X54,X58)
        | X58 != X59
        | ~ m1_subset_1(X59,u1_struct_0(X56))
        | ~ m1_subset_1(X58,u1_struct_0(X54))
        | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X54)))
        | v2_struct_0(X56)
        | ~ m1_pre_topc(X56,X54)
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,u1_struct_0(X54),u1_struct_0(X53))
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X54),u1_struct_0(X53))))
        | v2_struct_0(X54)
        | ~ v2_pre_topc(X54)
        | ~ l1_pre_topc(X54)
        | v2_struct_0(X53)
        | ~ v2_pre_topc(X53)
        | ~ l1_pre_topc(X53) )
      & ( ~ r1_tmap_1(X56,X53,k2_tmap_1(X54,X53,X55,X56),X59)
        | r1_tmap_1(X54,X53,X55,X58)
        | ~ r1_tarski(X57,u1_struct_0(X56))
        | ~ m1_connsp_2(X57,X54,X58)
        | X58 != X59
        | ~ m1_subset_1(X59,u1_struct_0(X56))
        | ~ m1_subset_1(X58,u1_struct_0(X54))
        | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X54)))
        | v2_struct_0(X56)
        | ~ m1_pre_topc(X56,X54)
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,u1_struct_0(X54),u1_struct_0(X53))
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X54),u1_struct_0(X53))))
        | v2_struct_0(X54)
        | ~ v2_pre_topc(X54)
        | ~ l1_pre_topc(X54)
        | v2_struct_0(X53)
        | ~ v2_pre_topc(X53)
        | ~ l1_pre_topc(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tmap_1])])])])])).

fof(c_0_57,plain,(
    ! [X30,X31,X32] :
      ( v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,u1_struct_0(X30))
      | ~ m1_connsp_2(X32,X30,X31)
      | m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

fof(c_0_58,plain,(
    ! [X23,X24,X25] :
      ( v2_struct_0(X23)
      | ~ l1_pre_topc(X23)
      | v2_struct_0(X24)
      | ~ m1_pre_topc(X24,X23)
      | ~ m1_subset_1(X25,u1_struct_0(X24))
      | m1_subset_1(X25,u1_struct_0(X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_59,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X4,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ r2_hidden(X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X4,X1) ),
    inference(csr,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_61,negated_conjecture,
    ( v3_pre_topc(esk7_0,X1)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_23])])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_63,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_64,plain,
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
    inference(csr,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_65,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X1)) = k2_tmap_1(esk5_0,esk2_0,esk6_0,X1)
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50]),c_0_31]),c_0_51]),c_0_52]),c_0_53])]),c_0_54]),c_0_55])).

cnf(c_0_66,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( m1_connsp_2(X1,X2,esk8_0)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(esk7_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_22]),c_0_62])])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk5_0,X2,esk6_0) = k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk5_0)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_53])]),c_0_54])).

cnf(c_0_73,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)) = k2_tmap_1(esk5_0,esk2_0,esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_30])).

fof(c_0_74,plain,(
    ! [X47,X48,X49,X50,X51,X52] :
      ( v2_struct_0(X47)
      | ~ v2_pre_topc(X47)
      | ~ l1_pre_topc(X47)
      | v2_struct_0(X48)
      | ~ v2_pre_topc(X48)
      | ~ l1_pre_topc(X48)
      | ~ v1_funct_1(X49)
      | ~ v1_funct_2(X49,u1_struct_0(X48),u1_struct_0(X47))
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X48),u1_struct_0(X47))))
      | v2_struct_0(X50)
      | ~ m1_pre_topc(X50,X48)
      | ~ m1_subset_1(X51,u1_struct_0(X48))
      | ~ m1_subset_1(X52,u1_struct_0(X50))
      | X51 != X52
      | ~ r1_tmap_1(X48,X47,X49,X51)
      | r1_tmap_1(X50,X47,k2_tmap_1(X48,X47,X49,X50),X52) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).

cnf(c_0_75,plain,
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
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_66,c_0_67])]),c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( m1_connsp_2(X1,esk5_0,esk8_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r1_tarski(esk7_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_31]),c_0_52]),c_0_62])]),c_0_55])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)
    | r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_79,negated_conjecture,
    ( esk8_0 = esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_80,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk5_0,esk4_0,esk6_0) = k2_tmap_1(esk5_0,esk2_0,esk6_0,esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_30]),c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_82,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,esk6_0,X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X2,esk2_0,k2_tmap_1(esk5_0,esk2_0,esk6_0,X2),X1)
    | ~ m1_connsp_2(X3,esk5_0,X1)
    | ~ m1_pre_topc(X2,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_tarski(X3,u1_struct_0(X2)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_48]),c_0_49]),c_0_31]),c_0_50]),c_0_52]),c_0_51]),c_0_53])]),c_0_54]),c_0_55])).

cnf(c_0_84,negated_conjecture,
    ( m1_connsp_2(esk7_0,esk5_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_62])])).

cnf(c_0_85,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk8_0)
    | r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0) = k2_tmap_1(esk5_0,esk2_0,esk6_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_22]),c_0_23]),c_0_38])]),c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_88,negated_conjecture,
    ( ~ r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)
    | ~ r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_89,plain,
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
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_82]),c_0_68])).

cnf(c_0_90,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(X1,esk2_0,k2_tmap_1(esk5_0,esk2_0,esk6_0,X1),esk8_0)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(esk8_0,u1_struct_0(X1))
    | ~ r1_tarski(esk7_0,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_91,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk5_0,esk2_0,esk6_0,esk4_0),esk8_0)
    | r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_87,c_0_79])).

cnf(c_0_93,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_94,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk8_0)
    | ~ r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_88,c_0_79])).

cnf(c_0_95,negated_conjecture,
    ( r1_tmap_1(X1,esk2_0,k2_tmap_1(esk5_0,esk2_0,esk6_0,X1),X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk5_0,esk2_0,esk6_0,X2)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_48]),c_0_49]),c_0_31]),c_0_50]),c_0_52]),c_0_51]),c_0_53])]),c_0_54]),c_0_55])).

cnf(c_0_96,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_30]),c_0_92]),c_0_33])]),c_0_93])).

cnf(c_0_97,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk5_0,esk2_0,esk6_0,esk4_0),esk8_0)
    | ~ r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_94,c_0_86])).

cnf(c_0_98,negated_conjecture,
    ( r1_tmap_1(X1,esk2_0,k2_tmap_1(esk5_0,esk2_0,esk6_0,X1),esk8_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(esk8_0,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_99,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk5_0,esk2_0,esk6_0,esk4_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_96])])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_30]),c_0_92])]),c_0_99]),c_0_93]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:31:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.20/0.41  # and selection function SelectCQIPrecWNTNp.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.030 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t85_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X2)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X1,X5,X7)<=>r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,X4,X3,X5),X8)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_tmap_1)).
% 0.20/0.41  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.41  fof(t33_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v3_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v3_pre_topc(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 0.20/0.41  fof(t39_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.20/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.41  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.20/0.41  fof(t8_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 0.20/0.41  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.41  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.20/0.41  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.20/0.41  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.20/0.41  fof(t65_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>(((r1_tarski(X5,u1_struct_0(X4))&m1_connsp_2(X5,X2,X6))&X6=X7)=>(r1_tmap_1(X2,X1,X3,X6)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X7)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 0.20/0.41  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.20/0.41  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.20/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.41  fof(t64_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>((X5=X6&r1_tmap_1(X2,X1,X3,X5))=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 0.20/0.41  fof(c_0_16, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X2)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X1,X5,X7)<=>r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,X4,X3,X5),X8))))))))))))), inference(assume_negation,[status(cth)],[t85_tmap_1])).
% 0.20/0.41  fof(c_0_17, plain, ![X18, X19]:(~l1_pre_topc(X18)|(~m1_pre_topc(X19,X18)|l1_pre_topc(X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.41  fof(c_0_18, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk3_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk2_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))))&(m1_pre_topc(esk4_0,esk5_0)&(m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk8_0,u1_struct_0(esk5_0))&(m1_subset_1(esk9_0,u1_struct_0(esk4_0))&((((v3_pre_topc(esk7_0,esk3_0)&r2_hidden(esk8_0,esk7_0))&r1_tarski(esk7_0,u1_struct_0(esk4_0)))&esk8_0=esk9_0)&((~r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)|~r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk9_0))&(r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)|r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk9_0))))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.20/0.41  fof(c_0_19, plain, ![X26, X27, X28, X29]:(~l1_pre_topc(X26)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~m1_pre_topc(X28,X26)|(~v3_pre_topc(X27,X26)|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|(X29!=X27|v3_pre_topc(X29,X28))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_tops_2])])])).
% 0.20/0.41  fof(c_0_20, plain, ![X20, X21, X22]:(~l1_pre_topc(X20)|(~m1_pre_topc(X21,X20)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).
% 0.20/0.41  cnf(c_0_21, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_22, negated_conjecture, (m1_pre_topc(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  fof(c_0_24, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.41  fof(c_0_25, plain, ![X16, X17]:(~v2_pre_topc(X16)|~l1_pre_topc(X16)|(~m1_pre_topc(X17,X16)|v2_pre_topc(X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.20/0.41  fof(c_0_26, plain, ![X33, X34, X35, X37]:(((((m1_subset_1(esk1_3(X33,X34,X35),k1_zfmisc_1(u1_struct_0(X33)))|~m1_connsp_2(X35,X33,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(v3_pre_topc(esk1_3(X33,X34,X35),X33)|~m1_connsp_2(X35,X33,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33))))&(r1_tarski(esk1_3(X33,X34,X35),X35)|~m1_connsp_2(X35,X33,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33))))&(r2_hidden(X34,esk1_3(X33,X34,X35))|~m1_connsp_2(X35,X33,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33))))&(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X33)))|~v3_pre_topc(X37,X33)|~r1_tarski(X37,X35)|~r2_hidden(X34,X37)|m1_connsp_2(X35,X33,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_connsp_2])])])])])])).
% 0.20/0.41  fof(c_0_27, plain, ![X13, X14, X15]:(~r2_hidden(X13,X14)|~m1_subset_1(X14,k1_zfmisc_1(X15))|m1_subset_1(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.41  cnf(c_0_28, plain, (v3_pre_topc(X4,X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X3,X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|X4!=X2), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_29, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_30, negated_conjecture, (m1_pre_topc(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_31, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.20/0.41  cnf(c_0_32, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (r1_tarski(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  fof(c_0_34, plain, ![X42, X43, X44, X45, X46]:(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)|(~m1_pre_topc(X44,X42)|(~m1_pre_topc(X45,X42)|(~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X43))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X43))))|(~m1_pre_topc(X45,X44)|k3_tmap_1(X42,X43,X44,X45,X46)=k2_partfun1(u1_struct_0(X44),u1_struct_0(X43),X46,u1_struct_0(X45)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.20/0.41  fof(c_0_35, plain, ![X60, X61, X62]:(~v2_pre_topc(X60)|~l1_pre_topc(X60)|(~m1_pre_topc(X61,X60)|(~m1_pre_topc(X62,X61)|m1_pre_topc(X62,X60)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.20/0.41  fof(c_0_36, plain, ![X38, X39, X40, X41]:(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|(~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X39))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X39))))|(~m1_pre_topc(X41,X38)|k2_tmap_1(X38,X39,X40,X41)=k2_partfun1(u1_struct_0(X38),u1_struct_0(X39),X40,u1_struct_0(X41)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.20/0.41  cnf(c_0_37, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_39, plain, (m1_connsp_2(X3,X2,X4)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|~r1_tarski(X1,X3)|~r2_hidden(X4,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  cnf(c_0_40, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.41  cnf(c_0_41, plain, (v3_pre_topc(X1,X2)|~v3_pre_topc(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_28]), c_0_29])).
% 0.20/0.41  cnf(c_0_42, negated_conjecture, (v3_pre_topc(esk7_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_43, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.20/0.41  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.41  cnf(c_0_45, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.41  cnf(c_0_46, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.41  cnf(c_0_47, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_49, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_50, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_51, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (v2_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_22]), c_0_23]), c_0_38])])).
% 0.20/0.41  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_54, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_55, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  fof(c_0_56, plain, ![X53, X54, X55, X56, X57, X58, X59]:((~r1_tmap_1(X54,X53,X55,X58)|r1_tmap_1(X56,X53,k2_tmap_1(X54,X53,X55,X56),X59)|(~r1_tarski(X57,u1_struct_0(X56))|~m1_connsp_2(X57,X54,X58)|X58!=X59)|~m1_subset_1(X59,u1_struct_0(X56))|~m1_subset_1(X58,u1_struct_0(X54))|~m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X54)))|(v2_struct_0(X56)|~m1_pre_topc(X56,X54))|(~v1_funct_1(X55)|~v1_funct_2(X55,u1_struct_0(X54),u1_struct_0(X53))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X54),u1_struct_0(X53)))))|(v2_struct_0(X54)|~v2_pre_topc(X54)|~l1_pre_topc(X54))|(v2_struct_0(X53)|~v2_pre_topc(X53)|~l1_pre_topc(X53)))&(~r1_tmap_1(X56,X53,k2_tmap_1(X54,X53,X55,X56),X59)|r1_tmap_1(X54,X53,X55,X58)|(~r1_tarski(X57,u1_struct_0(X56))|~m1_connsp_2(X57,X54,X58)|X58!=X59)|~m1_subset_1(X59,u1_struct_0(X56))|~m1_subset_1(X58,u1_struct_0(X54))|~m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X54)))|(v2_struct_0(X56)|~m1_pre_topc(X56,X54))|(~v1_funct_1(X55)|~v1_funct_2(X55,u1_struct_0(X54),u1_struct_0(X53))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X54),u1_struct_0(X53)))))|(v2_struct_0(X54)|~v2_pre_topc(X54)|~l1_pre_topc(X54))|(v2_struct_0(X53)|~v2_pre_topc(X53)|~l1_pre_topc(X53)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tmap_1])])])])])).
% 0.20/0.41  fof(c_0_57, plain, ![X30, X31, X32]:(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|~m1_subset_1(X31,u1_struct_0(X30))|(~m1_connsp_2(X32,X30,X31)|m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.20/0.41  fof(c_0_58, plain, ![X23, X24, X25]:(v2_struct_0(X23)|~l1_pre_topc(X23)|(v2_struct_0(X24)|~m1_pre_topc(X24,X23)|(~m1_subset_1(X25,u1_struct_0(X24))|m1_subset_1(X25,u1_struct_0(X23))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.20/0.41  cnf(c_0_59, plain, (m1_connsp_2(X1,X2,X3)|v2_struct_0(X2)|~v3_pre_topc(X4,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~r2_hidden(X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X4,X1)), inference(csr,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.41  cnf(c_0_60, negated_conjecture, (r2_hidden(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_61, negated_conjecture, (v3_pre_topc(esk7_0,X1)|~m1_pre_topc(X1,esk3_0)|~m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_23])])).
% 0.20/0.41  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.41  fof(c_0_63, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.41  cnf(c_0_64, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(csr,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.41  cnf(c_0_65, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X1))=k2_tmap_1(esk5_0,esk2_0,esk6_0,X1)|~m1_pre_topc(X1,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50]), c_0_31]), c_0_51]), c_0_52]), c_0_53])]), c_0_54]), c_0_55])).
% 0.20/0.41  cnf(c_0_66, plain, (r1_tmap_1(X3,X2,X4,X6)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|~r1_tarski(X7,u1_struct_0(X1))|~m1_connsp_2(X7,X3,X6)|X6!=X5|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.41  cnf(c_0_67, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.41  cnf(c_0_68, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.41  cnf(c_0_69, negated_conjecture, (m1_connsp_2(X1,X2,esk8_0)|v2_struct_0(X2)|~v3_pre_topc(esk7_0,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.41  cnf(c_0_70, negated_conjecture, (v3_pre_topc(esk7_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_22]), c_0_62])])).
% 0.20/0.41  cnf(c_0_71, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.41  cnf(c_0_72, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk5_0,X2,esk6_0)=k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk5_0)|~m1_pre_topc(esk5_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_53])]), c_0_54])).
% 0.20/0.41  cnf(c_0_73, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0))=k2_tmap_1(esk5_0,esk2_0,esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_65, c_0_30])).
% 0.20/0.41  fof(c_0_74, plain, ![X47, X48, X49, X50, X51, X52]:(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47)|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X48),u1_struct_0(X47))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X48),u1_struct_0(X47))))|(v2_struct_0(X50)|~m1_pre_topc(X50,X48)|(~m1_subset_1(X51,u1_struct_0(X48))|(~m1_subset_1(X52,u1_struct_0(X50))|(X51!=X52|~r1_tmap_1(X48,X47,X49,X51)|r1_tmap_1(X50,X47,k2_tmap_1(X48,X47,X49,X50),X52)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).
% 0.20/0.41  cnf(c_0_75, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X5)|~r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~m1_connsp_2(X6,X1,X4)|~m1_pre_topc(X5,X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~v2_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,u1_struct_0(X5))|~r1_tarski(X6,u1_struct_0(X5))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_66, c_0_67])]), c_0_68])).
% 0.20/0.41  cnf(c_0_76, negated_conjecture, (m1_connsp_2(X1,esk5_0,esk8_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~r1_tarski(esk7_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_31]), c_0_52]), c_0_62])]), c_0_55])).
% 0.20/0.41  cnf(c_0_77, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_71])).
% 0.20/0.41  cnf(c_0_78, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)|r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_79, negated_conjecture, (esk8_0=esk9_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_80, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk5_0,esk4_0,esk6_0)=k2_tmap_1(esk5_0,esk2_0,esk6_0,esk4_0)|v2_struct_0(X1)|~m1_pre_topc(esk5_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_30]), c_0_73])).
% 0.20/0.41  cnf(c_0_81, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_82, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X4)|r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X4,X2)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X6,u1_struct_0(X4))|X5!=X6|~r1_tmap_1(X2,X1,X3,X5)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.41  cnf(c_0_83, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,esk6_0,X1)|v2_struct_0(X2)|~r1_tmap_1(X2,esk2_0,k2_tmap_1(esk5_0,esk2_0,esk6_0,X2),X1)|~m1_connsp_2(X3,esk5_0,X1)|~m1_pre_topc(X2,esk5_0)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_tarski(X3,u1_struct_0(X2))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_48]), c_0_49]), c_0_31]), c_0_50]), c_0_52]), c_0_51]), c_0_53])]), c_0_54]), c_0_55])).
% 0.20/0.41  cnf(c_0_84, negated_conjecture, (m1_connsp_2(esk7_0,esk5_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_62])])).
% 0.20/0.41  cnf(c_0_85, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk8_0)|r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)), inference(rw,[status(thm)],[c_0_78, c_0_79])).
% 0.20/0.41  cnf(c_0_86, negated_conjecture, (k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0)=k2_tmap_1(esk5_0,esk2_0,esk6_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_22]), c_0_23]), c_0_38])]), c_0_81])).
% 0.20/0.41  cnf(c_0_87, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_88, negated_conjecture, (~r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)|~r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_89, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X3,X2,X4,X5)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X4)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X5,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_82]), c_0_68])).
% 0.20/0.41  cnf(c_0_90, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)|v2_struct_0(X1)|~r1_tmap_1(X1,esk2_0,k2_tmap_1(esk5_0,esk2_0,esk6_0,X1),esk8_0)|~m1_pre_topc(X1,esk5_0)|~m1_subset_1(esk8_0,u1_struct_0(X1))|~r1_tarski(esk7_0,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.20/0.41  cnf(c_0_91, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk5_0,esk2_0,esk6_0,esk4_0),esk8_0)|r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)), inference(rw,[status(thm)],[c_0_85, c_0_86])).
% 0.20/0.41  cnf(c_0_92, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_87, c_0_79])).
% 0.20/0.41  cnf(c_0_93, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_94, negated_conjecture, (~r1_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0,esk6_0),esk8_0)|~r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)), inference(rw,[status(thm)],[c_0_88, c_0_79])).
% 0.20/0.41  cnf(c_0_95, negated_conjecture, (r1_tmap_1(X1,esk2_0,k2_tmap_1(esk5_0,esk2_0,esk6_0,X1),X2)|v2_struct_0(X1)|~r1_tmap_1(esk5_0,esk2_0,esk6_0,X2)|~m1_pre_topc(X1,esk5_0)|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_48]), c_0_49]), c_0_31]), c_0_50]), c_0_52]), c_0_51]), c_0_53])]), c_0_54]), c_0_55])).
% 0.20/0.41  cnf(c_0_96, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_30]), c_0_92]), c_0_33])]), c_0_93])).
% 0.20/0.41  cnf(c_0_97, negated_conjecture, (~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk5_0,esk2_0,esk6_0,esk4_0),esk8_0)|~r1_tmap_1(esk5_0,esk2_0,esk6_0,esk8_0)), inference(rw,[status(thm)],[c_0_94, c_0_86])).
% 0.20/0.41  cnf(c_0_98, negated_conjecture, (r1_tmap_1(X1,esk2_0,k2_tmap_1(esk5_0,esk2_0,esk6_0,X1),esk8_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk5_0)|~m1_subset_1(esk8_0,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.20/0.41  cnf(c_0_99, negated_conjecture, (~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk5_0,esk2_0,esk6_0,esk4_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_96])])).
% 0.20/0.41  cnf(c_0_100, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_30]), c_0_92])]), c_0_99]), c_0_93]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 101
% 0.20/0.41  # Proof object clause steps            : 68
% 0.20/0.41  # Proof object formula steps           : 33
% 0.20/0.41  # Proof object conjectures             : 50
% 0.20/0.41  # Proof object clause conjectures      : 47
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 35
% 0.20/0.41  # Proof object initial formulas used   : 16
% 0.20/0.41  # Proof object generating inferences   : 21
% 0.20/0.41  # Proof object simplifying inferences  : 82
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 16
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 46
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 46
% 0.20/0.41  # Processed clauses                    : 548
% 0.20/0.41  # ...of these trivial                  : 12
% 0.20/0.41  # ...subsumed                          : 23
% 0.20/0.41  # ...remaining for further processing  : 513
% 0.20/0.41  # Other redundant clauses eliminated   : 6
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 0
% 0.20/0.41  # Backward-rewritten                   : 5
% 0.20/0.41  # Generated clauses                    : 708
% 0.20/0.41  # ...of the previous two non-trivial   : 525
% 0.20/0.41  # Contextual simplify-reflections      : 11
% 0.20/0.41  # Paramodulations                      : 702
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 6
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 458
% 0.20/0.41  #    Positive orientable unit clauses  : 251
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 5
% 0.20/0.41  #    Non-unit-clauses                  : 202
% 0.20/0.41  # Current number of unprocessed clauses: 67
% 0.20/0.41  # ...number of literals in the above   : 186
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 49
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 5691
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 1898
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 34
% 0.20/0.41  # Unit Clause-clause subsumption calls : 63
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 1060
% 0.20/0.41  # BW rewrite match successes           : 2
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 22644
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.069 s
% 0.20/0.41  # System time              : 0.007 s
% 0.20/0.41  # Total time               : 0.076 s
% 0.20/0.41  # Maximum resident set size: 1616 pages
%------------------------------------------------------------------------------
