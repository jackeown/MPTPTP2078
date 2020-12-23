%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:52 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  112 (6726 expanded)
%              Number of clauses        :   81 (2328 expanded)
%              Number of leaves         :   15 (1644 expanded)
%              Depth                    :   16
%              Number of atoms          :  693 (81082 expanded)
%              Number of equality atoms :   26 (3563 expanded)
%              Maximal formula depth    :   33 (   7 average)
%              Maximal clause size      :   46 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t86_tmap_1,conjecture,(
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
                     => ( ( v1_tsep_1(X3,X4)
                          & m1_pre_topc(X3,X4) )
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X4))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X3))
                               => ( X6 = X7
                                 => ( r1_tmap_1(X4,X2,X5,X6)
                                  <=> r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

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

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

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

fof(existence_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ? [X3] : m1_connsp_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

fof(t9_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ! [X5] :
                      ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( ( v3_pre_topc(X3,X1)
                          & r1_tarski(X3,u1_struct_0(X2))
                          & r1_tarski(X4,X3)
                          & X4 = X5 )
                       => ( v3_pre_topc(X5,X2)
                        <=> v3_pre_topc(X4,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tsep_1)).

fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

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

fof(t84_tmap_1,axiom,(
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
                     => ( m1_pre_topc(X3,X4)
                       => ! [X6] :
                            ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X4))
                               => ! [X8] :
                                    ( m1_subset_1(X8,u1_struct_0(X3))
                                   => ( ( v3_pre_topc(X6,X4)
                                        & r2_hidden(X7,X6)
                                        & r1_tarski(X6,u1_struct_0(X3))
                                        & X7 = X8 )
                                     => ( r1_tmap_1(X4,X2,X5,X7)
                                      <=> r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).

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

fof(t81_tmap_1,axiom,(
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
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X3))
                         => ! [X7] :
                              ( m1_subset_1(X7,u1_struct_0(X4))
                             => ( ( X6 = X7
                                  & m1_pre_topc(X4,X3)
                                  & r1_tmap_1(X3,X2,X5,X6) )
                               => r1_tmap_1(X4,X2,k3_tmap_1(X1,X2,X3,X4,X5),X7) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).

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
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                       => ( ( v1_tsep_1(X3,X4)
                            & m1_pre_topc(X3,X4) )
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X4))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X3))
                                 => ( X6 = X7
                                   => ( r1_tmap_1(X4,X2,X5,X6)
                                    <=> r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7) ) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t86_tmap_1])).

fof(c_0_16,plain,(
    ! [X31,X32,X33] :
      ( ( ~ v1_tsep_1(X32,X31)
        | ~ m1_pre_topc(X32,X31)
        | v3_pre_topc(X33,X31)
        | X33 != u1_struct_0(X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_pre_topc(X32,X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( v1_tsep_1(X32,X31)
        | ~ v3_pre_topc(X33,X31)
        | X33 != u1_struct_0(X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_pre_topc(X32,X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( m1_pre_topc(X32,X31)
        | ~ v3_pre_topc(X33,X31)
        | X33 != u1_struct_0(X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_pre_topc(X32,X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk3_0)
    & ~ v2_struct_0(esk6_0)
    & m1_pre_topc(esk6_0,esk3_0)
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,u1_struct_0(esk6_0),u1_struct_0(esk4_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0))))
    & v1_tsep_1(esk5_0,esk6_0)
    & m1_pre_topc(esk5_0,esk6_0)
    & m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    & m1_subset_1(esk9_0,u1_struct_0(esk5_0))
    & esk8_0 = esk9_0
    & ( ~ r1_tmap_1(esk6_0,esk4_0,esk7_0,esk8_0)
      | ~ r1_tmap_1(esk5_0,esk4_0,k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk7_0),esk9_0) )
    & ( r1_tmap_1(esk6_0,esk4_0,esk7_0,esk8_0)
      | r1_tmap_1(esk5_0,esk4_0,k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk7_0),esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | l1_pre_topc(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_19,plain,(
    ! [X13,X14] :
      ( ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(X14,X13)
      | v2_pre_topc(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_20,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X34,X35] :
      ( ~ l1_pre_topc(X34)
      | ~ m1_pre_topc(X35,X34)
      | m1_subset_1(u1_struct_0(X35),k1_zfmisc_1(u1_struct_0(X34))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_22,plain,(
    ! [X26,X27,X28,X30] :
      ( ( m1_subset_1(esk2_3(X26,X27,X28),k1_zfmisc_1(u1_struct_0(X26)))
        | ~ m1_connsp_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( v3_pre_topc(esk2_3(X26,X27,X28),X26)
        | ~ m1_connsp_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( r1_tarski(esk2_3(X26,X27,X28),X28)
        | ~ m1_connsp_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( r2_hidden(X27,esk2_3(X26,X27,X28))
        | ~ m1_connsp_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v3_pre_topc(X30,X26)
        | ~ r1_tarski(X30,X28)
        | ~ r2_hidden(X27,X30)
        | m1_connsp_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ m1_subset_1(X27,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_connsp_2])])])])])])).

fof(c_0_23,plain,(
    ! [X20,X21,X22] :
      ( v2_struct_0(X20)
      | ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | ~ m1_connsp_2(X22,X20,X21)
      | m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

fof(c_0_24,plain,(
    ! [X23,X24] :
      ( v2_struct_0(X23)
      | ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | m1_connsp_2(esk1_2(X23,X24),X23,X24) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m1_connsp_2])])])])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( esk8_0 = esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_32,plain,(
    ! [X54,X55,X56,X57,X58] :
      ( ( ~ v3_pre_topc(X58,X55)
        | v3_pre_topc(X57,X54)
        | ~ v3_pre_topc(X56,X54)
        | ~ r1_tarski(X56,u1_struct_0(X55))
        | ~ r1_tarski(X57,X56)
        | X57 != X58
        | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X55)))
        | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X54)))
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X54)))
        | ~ m1_pre_topc(X55,X54)
        | ~ v2_pre_topc(X54)
        | ~ l1_pre_topc(X54) )
      & ( ~ v3_pre_topc(X57,X54)
        | v3_pre_topc(X58,X55)
        | ~ v3_pre_topc(X56,X54)
        | ~ r1_tarski(X56,u1_struct_0(X55))
        | ~ r1_tarski(X57,X56)
        | X57 != X58
        | ~ m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X55)))
        | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X54)))
        | ~ m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X54)))
        | ~ m1_pre_topc(X55,X54)
        | ~ v2_pre_topc(X54)
        | ~ l1_pre_topc(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_tsep_1])])])])).

fof(c_0_33,plain,(
    ! [X17,X18,X19] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(X18,X17)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

cnf(c_0_34,plain,
    ( v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[c_0_20])).

cnf(c_0_35,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(esk1_2(X1,X2),X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_42,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_28]),c_0_29]),c_0_31])])).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,esk2_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_45,plain,
    ( v3_pre_topc(X3,X4)
    | ~ v3_pre_topc(X1,X2)
    | ~ v3_pre_topc(X5,X4)
    | ~ r1_tarski(X5,u1_struct_0(X2))
    | ~ r1_tarski(X3,X5)
    | X3 != X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X2,X4)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_49,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_50,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_36]),c_0_29])])).

cnf(c_0_51,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_36]),c_0_29]),c_0_31])])).

cnf(c_0_52,plain,
    ( v3_pre_topc(esk2_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_53,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_54,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_56,negated_conjecture,
    ( m1_connsp_2(esk1_2(esk5_0,esk8_0),esk5_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42])]),c_0_43])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,esk2_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X3,X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[c_0_44,c_0_38])).

cnf(c_0_58,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | ~ v3_pre_topc(X1,X4)
    | ~ m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ r1_tarski(X3,u1_struct_0(X4))
    | ~ r1_tarski(X1,X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_45]),c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk5_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50]),c_0_51])])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_49]),c_0_50])])).

cnf(c_0_61,plain,
    ( v3_pre_topc(esk2_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_52,c_0_38])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk2_3(esk5_0,esk8_0,esk1_2(esk5_0,esk8_0)),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_41]),c_0_42]),c_0_40])]),c_0_43])).

cnf(c_0_65,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk5_0,esk8_0,esk1_2(esk5_0,esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_56]),c_0_41]),c_0_42]),c_0_40])]),c_0_43])).

cnf(c_0_67,negated_conjecture,
    ( v3_pre_topc(X1,esk6_0)
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(u1_struct_0(esk5_0),u1_struct_0(X2))
    | ~ r1_tarski(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_50]),c_0_51]),c_0_60])])).

cnf(c_0_68,negated_conjecture,
    ( v3_pre_topc(esk2_3(esk5_0,esk8_0,esk1_2(esk5_0,esk8_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_56]),c_0_41]),c_0_42]),c_0_40])]),c_0_43])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk2_3(esk5_0,esk8_0,esk1_2(esk5_0,esk8_0)),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_49]),c_0_50])])).

fof(c_0_72,plain,(
    ! [X46,X47,X48,X49,X50,X51,X52,X53] :
      ( ( ~ r1_tmap_1(X49,X47,X50,X52)
        | r1_tmap_1(X48,X47,k3_tmap_1(X46,X47,X49,X48,X50),X53)
        | ~ v3_pre_topc(X51,X49)
        | ~ r2_hidden(X52,X51)
        | ~ r1_tarski(X51,u1_struct_0(X48))
        | X52 != X53
        | ~ m1_subset_1(X53,u1_struct_0(X48))
        | ~ m1_subset_1(X52,u1_struct_0(X49))
        | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))
        | ~ m1_pre_topc(X48,X49)
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,u1_struct_0(X49),u1_struct_0(X47))
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X47))))
        | v2_struct_0(X49)
        | ~ m1_pre_topc(X49,X46)
        | v2_struct_0(X48)
        | ~ m1_pre_topc(X48,X46)
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( ~ r1_tmap_1(X48,X47,k3_tmap_1(X46,X47,X49,X48,X50),X53)
        | r1_tmap_1(X49,X47,X50,X52)
        | ~ v3_pre_topc(X51,X49)
        | ~ r2_hidden(X52,X51)
        | ~ r1_tarski(X51,u1_struct_0(X48))
        | X52 != X53
        | ~ m1_subset_1(X53,u1_struct_0(X48))
        | ~ m1_subset_1(X52,u1_struct_0(X49))
        | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))
        | ~ m1_pre_topc(X48,X49)
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,u1_struct_0(X49),u1_struct_0(X47))
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X47))))
        | v2_struct_0(X49)
        | ~ m1_pre_topc(X49,X46)
        | v2_struct_0(X48)
        | ~ m1_pre_topc(X48,X46)
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t84_tmap_1])])])])])).

fof(c_0_73,plain,(
    ! [X36,X37,X38] :
      ( ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | ~ m1_pre_topc(X37,X36)
      | ~ m1_pre_topc(X38,X37)
      | m1_pre_topc(X38,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

cnf(c_0_74,negated_conjecture,
    ( m1_connsp_2(X1,X2,esk8_0)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(esk2_3(esk5_0,esk8_0,esk1_2(esk5_0,esk8_0)),X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(esk2_3(esk5_0,esk8_0,esk1_2(esk5_0,esk8_0)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(esk8_0,u1_struct_0(X2))
    | ~ r1_tarski(esk2_3(esk5_0,esk8_0,esk1_2(esk5_0,esk8_0)),X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( v3_pre_topc(esk2_3(esk5_0,esk8_0,esk1_2(esk5_0,esk8_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_49]),c_0_64]),c_0_69]),c_0_70])])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk2_3(esk5_0,esk8_0,esk1_2(esk5_0,esk8_0)),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_64])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_78,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_79,plain,
    ( r1_tmap_1(X4,X2,X5,X7)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)
    | ~ v3_pre_topc(X8,X4)
    | ~ r2_hidden(X7,X8)
    | ~ r1_tarski(X8,u1_struct_0(X1))
    | X7 != X6
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X7,u1_struct_0(X4))
    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X1,X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_80,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( m1_connsp_2(X1,esk6_0,esk8_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ r1_tarski(esk2_3(esk5_0,esk8_0,esk1_2(esk5_0,esk8_0)),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_50]),c_0_51]),c_0_76]),c_0_77])]),c_0_78])).

fof(c_0_82,plain,(
    ! [X39,X40,X41,X42,X43,X44,X45] :
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
      | ~ v1_funct_2(X43,u1_struct_0(X41),u1_struct_0(X40))
      | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X40))))
      | ~ m1_subset_1(X44,u1_struct_0(X41))
      | ~ m1_subset_1(X45,u1_struct_0(X42))
      | X44 != X45
      | ~ m1_pre_topc(X42,X41)
      | ~ r1_tmap_1(X41,X40,X43,X44)
      | r1_tmap_1(X42,X40,k3_tmap_1(X39,X40,X41,X42,X43),X45) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t81_tmap_1])])])])).

cnf(c_0_83,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X6)
    | ~ r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ r2_hidden(X4,X7)
    | ~ v3_pre_topc(X7,X1)
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X6,X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X6))
    | ~ r1_tarski(X7,u1_struct_0(X6)) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_79,c_0_80])])).

cnf(c_0_84,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk6_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_85,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_86,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_87,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_89,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_90,negated_conjecture,
    ( m1_connsp_2(u1_struct_0(esk5_0),esk6_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_70]),c_0_60])])).

cnf(c_0_91,plain,
    ( r1_tarski(esk2_3(X1,X2,X3),X3)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_92,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | r1_tmap_1(X4,X2,k3_tmap_1(X1,X2,X3,X4,X5),X7)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ m1_subset_1(X7,u1_struct_0(X4))
    | X6 != X7
    | ~ m1_pre_topc(X4,X3)
    | ~ r1_tmap_1(X3,X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_93,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk4_0,esk7_0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X3,esk4_0,k3_tmap_1(X2,esk4_0,esk6_0,X3,esk7_0),X1)
    | ~ r2_hidden(X1,X4)
    | ~ v3_pre_topc(X4,esk6_0)
    | ~ m1_pre_topc(esk6_0,X2)
    | ~ m1_pre_topc(X3,esk6_0)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ r1_tarski(X4,u1_struct_0(X3)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85]),c_0_86]),c_0_87]),c_0_88])]),c_0_89]),c_0_78])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(esk8_0,esk2_3(esk6_0,esk8_0,u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_90]),c_0_50]),c_0_51]),c_0_77])]),c_0_78])).

cnf(c_0_95,negated_conjecture,
    ( v3_pre_topc(esk2_3(esk6_0,esk8_0,u1_struct_0(esk5_0)),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_90]),c_0_50]),c_0_51]),c_0_77])]),c_0_78])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(esk2_3(esk6_0,esk8_0,u1_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_90]),c_0_50]),c_0_51]),c_0_77])]),c_0_78])).

cnf(c_0_97,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk4_0,esk7_0,esk8_0)
    | r1_tmap_1(esk5_0,esk4_0,k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk7_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_98,plain,
    ( v2_struct_0(X1)
    | r1_tarski(esk2_3(X1,X2,X3),X3)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_91,c_0_38])).

cnf(c_0_99,plain,
    ( r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X4,X2,X5,X6)
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_pre_topc(X4,X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X6,u1_struct_0(X4)) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_92,c_0_80])])).

cnf(c_0_100,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk4_0,esk7_0,esk8_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,esk4_0,k3_tmap_1(X2,esk4_0,esk6_0,X1,esk7_0),esk8_0)
    | ~ m1_pre_topc(esk6_0,X2)
    | ~ m1_pre_topc(X1,esk6_0)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(esk8_0,u1_struct_0(X1))
    | ~ r1_tarski(esk2_3(esk6_0,esk8_0,u1_struct_0(esk5_0)),u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95]),c_0_96]),c_0_77])])).

cnf(c_0_101,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk4_0,k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk7_0),esk8_0)
    | r1_tmap_1(esk6_0,esk4_0,esk7_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_97,c_0_26])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(esk2_3(esk6_0,esk8_0,u1_struct_0(esk5_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_90]),c_0_50]),c_0_51]),c_0_77])]),c_0_78])).

cnf(c_0_103,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_104,negated_conjecture,
    ( r1_tmap_1(X1,esk4_0,k3_tmap_1(X2,esk4_0,esk6_0,X1,esk7_0),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(esk6_0,esk4_0,esk7_0,X3)
    | ~ m1_pre_topc(X1,esk6_0)
    | ~ m1_pre_topc(esk6_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_84]),c_0_85]),c_0_86]),c_0_87]),c_0_88])]),c_0_89]),c_0_78])).

cnf(c_0_105,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk4_0,esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_36]),c_0_49]),c_0_29]),c_0_31]),c_0_40]),c_0_102])]),c_0_43]),c_0_103])).

cnf(c_0_106,negated_conjecture,
    ( ~ r1_tmap_1(esk6_0,esk4_0,esk7_0,esk8_0)
    | ~ r1_tmap_1(esk5_0,esk4_0,k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk7_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_107,negated_conjecture,
    ( r1_tmap_1(X1,esk4_0,k3_tmap_1(X2,esk4_0,esk6_0,X1,esk7_0),esk8_0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk6_0)
    | ~ m1_pre_topc(esk6_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(esk8_0,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_77])])).

cnf(c_0_108,negated_conjecture,
    ( ~ r1_tmap_1(esk5_0,esk4_0,k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk7_0),esk8_0)
    | ~ r1_tmap_1(esk6_0,esk4_0,esk7_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_106,c_0_26])).

cnf(c_0_109,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk4_0,k3_tmap_1(X1,esk4_0,esk6_0,esk5_0,esk7_0),esk8_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk6_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_49]),c_0_40])]),c_0_43])).

cnf(c_0_110,negated_conjecture,
    ( ~ r1_tmap_1(esk5_0,esk4_0,k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk7_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_105])])).

cnf(c_0_111,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_36]),c_0_29]),c_0_31])]),c_0_110]),c_0_103]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:49:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.45  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.19/0.45  # and selection function SelectCQIPrecWNTNp.
% 0.19/0.45  #
% 0.19/0.45  # Preprocessing time       : 0.030 s
% 0.19/0.45  # Presaturation interreduction done
% 0.19/0.45  
% 0.19/0.45  # Proof found!
% 0.19/0.45  # SZS status Theorem
% 0.19/0.45  # SZS output start CNFRefutation
% 0.19/0.45  fof(t86_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((v1_tsep_1(X3,X4)&m1_pre_topc(X3,X4))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>(X6=X7=>(r1_tmap_1(X4,X2,X5,X6)<=>r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 0.19/0.45  fof(t16_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 0.19/0.45  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.45  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.19/0.45  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.19/0.45  fof(t8_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 0.19/0.45  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.19/0.45  fof(existence_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>?[X3]:m1_connsp_2(X3,X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 0.19/0.45  fof(t9_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>((((v3_pre_topc(X3,X1)&r1_tarski(X3,u1_struct_0(X2)))&r1_tarski(X4,X3))&X4=X5)=>(v3_pre_topc(X5,X2)<=>v3_pre_topc(X4,X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_tsep_1)).
% 0.19/0.45  fof(t39_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.19/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.45  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.45  fof(t84_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X4)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X2,X5,X7)<=>r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 0.19/0.45  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.19/0.45  fof(t81_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X6]:(m1_subset_1(X6,u1_struct_0(X3))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>(((X6=X7&m1_pre_topc(X4,X3))&r1_tmap_1(X3,X2,X5,X6))=>r1_tmap_1(X4,X2,k3_tmap_1(X1,X2,X3,X4,X5),X7))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 0.19/0.45  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((v1_tsep_1(X3,X4)&m1_pre_topc(X3,X4))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>(X6=X7=>(r1_tmap_1(X4,X2,X5,X6)<=>r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7)))))))))))), inference(assume_negation,[status(cth)],[t86_tmap_1])).
% 0.19/0.45  fof(c_0_16, plain, ![X31, X32, X33]:((~v1_tsep_1(X32,X31)|~m1_pre_topc(X32,X31)|v3_pre_topc(X33,X31)|X33!=u1_struct_0(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|~m1_pre_topc(X32,X31)|(~v2_pre_topc(X31)|~l1_pre_topc(X31)))&((v1_tsep_1(X32,X31)|~v3_pre_topc(X33,X31)|X33!=u1_struct_0(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|~m1_pre_topc(X32,X31)|(~v2_pre_topc(X31)|~l1_pre_topc(X31)))&(m1_pre_topc(X32,X31)|~v3_pre_topc(X33,X31)|X33!=u1_struct_0(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|~m1_pre_topc(X32,X31)|(~v2_pre_topc(X31)|~l1_pre_topc(X31))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).
% 0.19/0.45  fof(c_0_17, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk3_0))&((~v2_struct_0(esk6_0)&m1_pre_topc(esk6_0,esk3_0))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(esk6_0),u1_struct_0(esk4_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0)))))&((v1_tsep_1(esk5_0,esk6_0)&m1_pre_topc(esk5_0,esk6_0))&(m1_subset_1(esk8_0,u1_struct_0(esk6_0))&(m1_subset_1(esk9_0,u1_struct_0(esk5_0))&(esk8_0=esk9_0&((~r1_tmap_1(esk6_0,esk4_0,esk7_0,esk8_0)|~r1_tmap_1(esk5_0,esk4_0,k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk7_0),esk9_0))&(r1_tmap_1(esk6_0,esk4_0,esk7_0,esk8_0)|r1_tmap_1(esk5_0,esk4_0,k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk7_0),esk9_0)))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.19/0.45  fof(c_0_18, plain, ![X15, X16]:(~l1_pre_topc(X15)|(~m1_pre_topc(X16,X15)|l1_pre_topc(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.45  fof(c_0_19, plain, ![X13, X14]:(~v2_pre_topc(X13)|~l1_pre_topc(X13)|(~m1_pre_topc(X14,X13)|v2_pre_topc(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.19/0.45  cnf(c_0_20, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.45  fof(c_0_21, plain, ![X34, X35]:(~l1_pre_topc(X34)|(~m1_pre_topc(X35,X34)|m1_subset_1(u1_struct_0(X35),k1_zfmisc_1(u1_struct_0(X34))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.19/0.45  fof(c_0_22, plain, ![X26, X27, X28, X30]:(((((m1_subset_1(esk2_3(X26,X27,X28),k1_zfmisc_1(u1_struct_0(X26)))|~m1_connsp_2(X28,X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(v3_pre_topc(esk2_3(X26,X27,X28),X26)|~m1_connsp_2(X28,X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26))))&(r1_tarski(esk2_3(X26,X27,X28),X28)|~m1_connsp_2(X28,X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26))))&(r2_hidden(X27,esk2_3(X26,X27,X28))|~m1_connsp_2(X28,X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26))))&(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X26)))|~v3_pre_topc(X30,X26)|~r1_tarski(X30,X28)|~r2_hidden(X27,X30)|m1_connsp_2(X28,X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|~m1_subset_1(X27,u1_struct_0(X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_connsp_2])])])])])])).
% 0.19/0.45  fof(c_0_23, plain, ![X20, X21, X22]:(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|~m1_subset_1(X21,u1_struct_0(X20))|(~m1_connsp_2(X22,X20,X21)|m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.19/0.45  fof(c_0_24, plain, ![X23, X24]:(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)|~m1_subset_1(X24,u1_struct_0(X23))|m1_connsp_2(esk1_2(X23,X24),X23,X24)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m1_connsp_2])])])])).
% 0.19/0.45  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_26, negated_conjecture, (esk8_0=esk9_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_27, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.45  cnf(c_0_28, negated_conjecture, (m1_pre_topc(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_30, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  cnf(c_0_31, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  fof(c_0_32, plain, ![X54, X55, X56, X57, X58]:((~v3_pre_topc(X58,X55)|v3_pre_topc(X57,X54)|(~v3_pre_topc(X56,X54)|~r1_tarski(X56,u1_struct_0(X55))|~r1_tarski(X57,X56)|X57!=X58)|~m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X55)))|~m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X54)))|~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X54)))|~m1_pre_topc(X55,X54)|(~v2_pre_topc(X54)|~l1_pre_topc(X54)))&(~v3_pre_topc(X57,X54)|v3_pre_topc(X58,X55)|(~v3_pre_topc(X56,X54)|~r1_tarski(X56,u1_struct_0(X55))|~r1_tarski(X57,X56)|X57!=X58)|~m1_subset_1(X58,k1_zfmisc_1(u1_struct_0(X55)))|~m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X54)))|~m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X54)))|~m1_pre_topc(X55,X54)|(~v2_pre_topc(X54)|~l1_pre_topc(X54)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_tsep_1])])])])).
% 0.19/0.45  fof(c_0_33, plain, ![X17, X18, X19]:(~l1_pre_topc(X17)|(~m1_pre_topc(X18,X17)|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).
% 0.19/0.45  cnf(c_0_34, plain, (v3_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X1,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[c_0_20])).
% 0.19/0.45  cnf(c_0_35, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.45  cnf(c_0_36, negated_conjecture, (m1_pre_topc(esk6_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_37, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~m1_connsp_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.45  cnf(c_0_38, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.45  cnf(c_0_39, plain, (v2_struct_0(X1)|m1_connsp_2(esk1_2(X1,X2),X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.45  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.45  cnf(c_0_41, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.19/0.45  cnf(c_0_42, negated_conjecture, (v2_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_28]), c_0_29]), c_0_31])])).
% 0.19/0.45  cnf(c_0_43, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_44, plain, (r2_hidden(X1,esk2_3(X2,X1,X3))|v2_struct_0(X2)|~m1_connsp_2(X3,X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.45  cnf(c_0_45, plain, (v3_pre_topc(X3,X4)|~v3_pre_topc(X1,X2)|~v3_pre_topc(X5,X4)|~r1_tarski(X5,u1_struct_0(X2))|~r1_tarski(X3,X5)|X3!=X1|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))|~m1_pre_topc(X2,X4)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.45  cnf(c_0_46, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.45  cnf(c_0_47, plain, (v3_pre_topc(u1_struct_0(X1),X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_34]), c_0_35])).
% 0.19/0.45  cnf(c_0_48, negated_conjecture, (v1_tsep_1(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_49, negated_conjecture, (m1_pre_topc(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_50, negated_conjecture, (l1_pre_topc(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_36]), c_0_29])])).
% 0.19/0.45  cnf(c_0_51, negated_conjecture, (v2_pre_topc(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_36]), c_0_29]), c_0_31])])).
% 0.19/0.45  cnf(c_0_52, plain, (v3_pre_topc(esk2_3(X1,X2,X3),X1)|v2_struct_0(X1)|~m1_connsp_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.45  fof(c_0_53, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.45  fof(c_0_54, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.45  cnf(c_0_55, plain, (v2_struct_0(X1)|m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~m1_connsp_2(X3,X1,X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.45  cnf(c_0_56, negated_conjecture, (m1_connsp_2(esk1_2(esk5_0,esk8_0),esk5_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42])]), c_0_43])).
% 0.19/0.45  cnf(c_0_57, plain, (r2_hidden(X1,esk2_3(X2,X1,X3))|v2_struct_0(X2)|~m1_connsp_2(X3,X2,X1)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(X1,u1_struct_0(X2))), inference(csr,[status(thm)],[c_0_44, c_0_38])).
% 0.19/0.45  cnf(c_0_58, plain, (v3_pre_topc(X1,X2)|~v3_pre_topc(X3,X2)|~v3_pre_topc(X1,X4)|~m1_pre_topc(X4,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X4)))|~r1_tarski(X3,u1_struct_0(X4))|~r1_tarski(X1,X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_45]), c_0_46])).
% 0.19/0.45  cnf(c_0_59, negated_conjecture, (v3_pre_topc(u1_struct_0(esk5_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50]), c_0_51])])).
% 0.19/0.45  cnf(c_0_60, negated_conjecture, (m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_49]), c_0_50])])).
% 0.19/0.45  cnf(c_0_61, plain, (v3_pre_topc(esk2_3(X1,X2,X3),X1)|v2_struct_0(X1)|~m1_connsp_2(X3,X1,X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_52, c_0_38])).
% 0.19/0.45  cnf(c_0_62, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.45  cnf(c_0_63, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.45  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk2_3(esk5_0,esk8_0,esk1_2(esk5_0,esk8_0)),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_41]), c_0_42]), c_0_40])]), c_0_43])).
% 0.19/0.45  cnf(c_0_65, plain, (m1_connsp_2(X3,X2,X4)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|~r1_tarski(X1,X3)|~r2_hidden(X4,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.45  cnf(c_0_66, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk5_0,esk8_0,esk1_2(esk5_0,esk8_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_56]), c_0_41]), c_0_42]), c_0_40])]), c_0_43])).
% 0.19/0.45  cnf(c_0_67, negated_conjecture, (v3_pre_topc(X1,esk6_0)|~v3_pre_topc(X1,X2)|~m1_pre_topc(X2,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(u1_struct_0(esk5_0),u1_struct_0(X2))|~r1_tarski(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_50]), c_0_51]), c_0_60])])).
% 0.19/0.45  cnf(c_0_68, negated_conjecture, (v3_pre_topc(esk2_3(esk5_0,esk8_0,esk1_2(esk5_0,esk8_0)),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_56]), c_0_41]), c_0_42]), c_0_40])]), c_0_43])).
% 0.19/0.45  cnf(c_0_69, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_62])).
% 0.19/0.45  cnf(c_0_70, negated_conjecture, (r1_tarski(esk2_3(esk5_0,esk8_0,esk1_2(esk5_0,esk8_0)),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.45  cnf(c_0_71, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_49]), c_0_50])])).
% 0.19/0.45  fof(c_0_72, plain, ![X46, X47, X48, X49, X50, X51, X52, X53]:((~r1_tmap_1(X49,X47,X50,X52)|r1_tmap_1(X48,X47,k3_tmap_1(X46,X47,X49,X48,X50),X53)|(~v3_pre_topc(X51,X49)|~r2_hidden(X52,X51)|~r1_tarski(X51,u1_struct_0(X48))|X52!=X53)|~m1_subset_1(X53,u1_struct_0(X48))|~m1_subset_1(X52,u1_struct_0(X49))|~m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))|~m1_pre_topc(X48,X49)|(~v1_funct_1(X50)|~v1_funct_2(X50,u1_struct_0(X49),u1_struct_0(X47))|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X47)))))|(v2_struct_0(X49)|~m1_pre_topc(X49,X46))|(v2_struct_0(X48)|~m1_pre_topc(X48,X46))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46)))&(~r1_tmap_1(X48,X47,k3_tmap_1(X46,X47,X49,X48,X50),X53)|r1_tmap_1(X49,X47,X50,X52)|(~v3_pre_topc(X51,X49)|~r2_hidden(X52,X51)|~r1_tarski(X51,u1_struct_0(X48))|X52!=X53)|~m1_subset_1(X53,u1_struct_0(X48))|~m1_subset_1(X52,u1_struct_0(X49))|~m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))|~m1_pre_topc(X48,X49)|(~v1_funct_1(X50)|~v1_funct_2(X50,u1_struct_0(X49),u1_struct_0(X47))|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X47)))))|(v2_struct_0(X49)|~m1_pre_topc(X49,X46))|(v2_struct_0(X48)|~m1_pre_topc(X48,X46))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t84_tmap_1])])])])])).
% 0.19/0.45  fof(c_0_73, plain, ![X36, X37, X38]:(~v2_pre_topc(X36)|~l1_pre_topc(X36)|(~m1_pre_topc(X37,X36)|(~m1_pre_topc(X38,X37)|m1_pre_topc(X38,X36)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.19/0.45  cnf(c_0_74, negated_conjecture, (m1_connsp_2(X1,X2,esk8_0)|v2_struct_0(X2)|~v3_pre_topc(esk2_3(esk5_0,esk8_0,esk1_2(esk5_0,esk8_0)),X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(esk2_3(esk5_0,esk8_0,esk1_2(esk5_0,esk8_0)),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(esk8_0,u1_struct_0(X2))|~r1_tarski(esk2_3(esk5_0,esk8_0,esk1_2(esk5_0,esk8_0)),X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.45  cnf(c_0_75, negated_conjecture, (v3_pre_topc(esk2_3(esk5_0,esk8_0,esk1_2(esk5_0,esk8_0)),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_49]), c_0_64]), c_0_69]), c_0_70])])).
% 0.19/0.45  cnf(c_0_76, negated_conjecture, (m1_subset_1(esk2_3(esk5_0,esk8_0,esk1_2(esk5_0,esk8_0)),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_71, c_0_64])).
% 0.19/0.45  cnf(c_0_77, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_78, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_79, plain, (r1_tmap_1(X4,X2,X5,X7)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)|~v3_pre_topc(X8,X4)|~r2_hidden(X7,X8)|~r1_tarski(X8,u1_struct_0(X1))|X7!=X6|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X7,u1_struct_0(X4))|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X4)))|~m1_pre_topc(X1,X4)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.45  cnf(c_0_80, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.45  cnf(c_0_81, negated_conjecture, (m1_connsp_2(X1,esk6_0,esk8_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))|~r1_tarski(esk2_3(esk5_0,esk8_0,esk1_2(esk5_0,esk8_0)),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_50]), c_0_51]), c_0_76]), c_0_77])]), c_0_78])).
% 0.19/0.45  fof(c_0_82, plain, ![X39, X40, X41, X42, X43, X44, X45]:(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|(v2_struct_0(X41)|~m1_pre_topc(X41,X39)|(v2_struct_0(X42)|~m1_pre_topc(X42,X39)|(~v1_funct_1(X43)|~v1_funct_2(X43,u1_struct_0(X41),u1_struct_0(X40))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X40))))|(~m1_subset_1(X44,u1_struct_0(X41))|(~m1_subset_1(X45,u1_struct_0(X42))|(X44!=X45|~m1_pre_topc(X42,X41)|~r1_tmap_1(X41,X40,X43,X44)|r1_tmap_1(X42,X40,k3_tmap_1(X39,X40,X41,X42,X43),X45))))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t81_tmap_1])])])])).
% 0.19/0.45  cnf(c_0_83, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X5)|v2_struct_0(X2)|v2_struct_0(X6)|~r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~r2_hidden(X4,X7)|~v3_pre_topc(X7,X1)|~m1_pre_topc(X1,X5)|~m1_pre_topc(X6,X1)|~l1_pre_topc(X5)|~l1_pre_topc(X2)|~v2_pre_topc(X5)|~v2_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X6))|~r1_tarski(X7,u1_struct_0(X6))), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_79, c_0_80])])).
% 0.19/0.45  cnf(c_0_84, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk6_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_85, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_86, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_87, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_88, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_89, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_90, negated_conjecture, (m1_connsp_2(u1_struct_0(esk5_0),esk6_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_70]), c_0_60])])).
% 0.19/0.45  cnf(c_0_91, plain, (r1_tarski(esk2_3(X1,X2,X3),X3)|v2_struct_0(X1)|~m1_connsp_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.45  cnf(c_0_92, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|r1_tmap_1(X4,X2,k3_tmap_1(X1,X2,X3,X4,X5),X7)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X7,u1_struct_0(X4))|X6!=X7|~m1_pre_topc(X4,X3)|~r1_tmap_1(X3,X2,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.19/0.45  cnf(c_0_93, negated_conjecture, (r1_tmap_1(esk6_0,esk4_0,esk7_0,X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X3,esk4_0,k3_tmap_1(X2,esk4_0,esk6_0,X3,esk7_0),X1)|~r2_hidden(X1,X4)|~v3_pre_topc(X4,esk6_0)|~m1_pre_topc(esk6_0,X2)|~m1_pre_topc(X3,esk6_0)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(esk6_0)))|~m1_subset_1(X1,u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(X3))|~r1_tarski(X4,u1_struct_0(X3))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85]), c_0_86]), c_0_87]), c_0_88])]), c_0_89]), c_0_78])).
% 0.19/0.45  cnf(c_0_94, negated_conjecture, (r2_hidden(esk8_0,esk2_3(esk6_0,esk8_0,u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_90]), c_0_50]), c_0_51]), c_0_77])]), c_0_78])).
% 0.19/0.45  cnf(c_0_95, negated_conjecture, (v3_pre_topc(esk2_3(esk6_0,esk8_0,u1_struct_0(esk5_0)),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_90]), c_0_50]), c_0_51]), c_0_77])]), c_0_78])).
% 0.19/0.45  cnf(c_0_96, negated_conjecture, (m1_subset_1(esk2_3(esk6_0,esk8_0,u1_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_90]), c_0_50]), c_0_51]), c_0_77])]), c_0_78])).
% 0.19/0.45  cnf(c_0_97, negated_conjecture, (r1_tmap_1(esk6_0,esk4_0,esk7_0,esk8_0)|r1_tmap_1(esk5_0,esk4_0,k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk7_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_98, plain, (v2_struct_0(X1)|r1_tarski(esk2_3(X1,X2,X3),X3)|~m1_connsp_2(X3,X1,X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_91, c_0_38])).
% 0.19/0.45  cnf(c_0_99, plain, (r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X4,X2,X5,X6)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_pre_topc(X1,X4)|~m1_pre_topc(X4,X3)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~v2_pre_topc(X3)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X6,u1_struct_0(X4))), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_92, c_0_80])])).
% 0.19/0.45  cnf(c_0_100, negated_conjecture, (r1_tmap_1(esk6_0,esk4_0,esk7_0,esk8_0)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tmap_1(X1,esk4_0,k3_tmap_1(X2,esk4_0,esk6_0,X1,esk7_0),esk8_0)|~m1_pre_topc(esk6_0,X2)|~m1_pre_topc(X1,esk6_0)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(esk8_0,u1_struct_0(X1))|~r1_tarski(esk2_3(esk6_0,esk8_0,u1_struct_0(esk5_0)),u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95]), c_0_96]), c_0_77])])).
% 0.19/0.45  cnf(c_0_101, negated_conjecture, (r1_tmap_1(esk5_0,esk4_0,k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk7_0),esk8_0)|r1_tmap_1(esk6_0,esk4_0,esk7_0,esk8_0)), inference(rw,[status(thm)],[c_0_97, c_0_26])).
% 0.19/0.45  cnf(c_0_102, negated_conjecture, (r1_tarski(esk2_3(esk6_0,esk8_0,u1_struct_0(esk5_0)),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_90]), c_0_50]), c_0_51]), c_0_77])]), c_0_78])).
% 0.19/0.45  cnf(c_0_103, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_104, negated_conjecture, (r1_tmap_1(X1,esk4_0,k3_tmap_1(X2,esk4_0,esk6_0,X1,esk7_0),X3)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tmap_1(esk6_0,esk4_0,esk7_0,X3)|~m1_pre_topc(X1,esk6_0)|~m1_pre_topc(esk6_0,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(esk6_0))|~m1_subset_1(X3,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_84]), c_0_85]), c_0_86]), c_0_87]), c_0_88])]), c_0_89]), c_0_78])).
% 0.19/0.45  cnf(c_0_105, negated_conjecture, (r1_tmap_1(esk6_0,esk4_0,esk7_0,esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_36]), c_0_49]), c_0_29]), c_0_31]), c_0_40]), c_0_102])]), c_0_43]), c_0_103])).
% 0.19/0.45  cnf(c_0_106, negated_conjecture, (~r1_tmap_1(esk6_0,esk4_0,esk7_0,esk8_0)|~r1_tmap_1(esk5_0,esk4_0,k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk7_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_107, negated_conjecture, (r1_tmap_1(X1,esk4_0,k3_tmap_1(X2,esk4_0,esk6_0,X1,esk7_0),esk8_0)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X1,esk6_0)|~m1_pre_topc(esk6_0,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(esk8_0,u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_77])])).
% 0.19/0.45  cnf(c_0_108, negated_conjecture, (~r1_tmap_1(esk5_0,esk4_0,k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk7_0),esk8_0)|~r1_tmap_1(esk6_0,esk4_0,esk7_0,esk8_0)), inference(rw,[status(thm)],[c_0_106, c_0_26])).
% 0.19/0.45  cnf(c_0_109, negated_conjecture, (r1_tmap_1(esk5_0,esk4_0,k3_tmap_1(X1,esk4_0,esk6_0,esk5_0,esk7_0),esk8_0)|v2_struct_0(X1)|~m1_pre_topc(esk6_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_49]), c_0_40])]), c_0_43])).
% 0.19/0.45  cnf(c_0_110, negated_conjecture, (~r1_tmap_1(esk5_0,esk4_0,k3_tmap_1(esk3_0,esk4_0,esk6_0,esk5_0,esk7_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_105])])).
% 0.19/0.45  cnf(c_0_111, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_36]), c_0_29]), c_0_31])]), c_0_110]), c_0_103]), ['proof']).
% 0.19/0.45  # SZS output end CNFRefutation
% 0.19/0.45  # Proof object total steps             : 112
% 0.19/0.45  # Proof object clause steps            : 81
% 0.19/0.45  # Proof object formula steps           : 31
% 0.19/0.45  # Proof object conjectures             : 56
% 0.19/0.45  # Proof object clause conjectures      : 53
% 0.19/0.45  # Proof object formula conjectures     : 3
% 0.19/0.45  # Proof object initial clauses used    : 38
% 0.19/0.45  # Proof object initial formulas used   : 15
% 0.19/0.45  # Proof object generating inferences   : 29
% 0.19/0.45  # Proof object simplifying inferences  : 130
% 0.19/0.45  # Training examples: 0 positive, 0 negative
% 0.19/0.45  # Parsed axioms                        : 15
% 0.19/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.45  # Initial clauses                      : 45
% 0.19/0.45  # Removed in clause preprocessing      : 1
% 0.19/0.45  # Initial clauses in saturation        : 44
% 0.19/0.45  # Processed clauses                    : 630
% 0.19/0.45  # ...of these trivial                  : 28
% 0.19/0.45  # ...subsumed                          : 81
% 0.19/0.45  # ...remaining for further processing  : 521
% 0.19/0.45  # Other redundant clauses eliminated   : 9
% 0.19/0.45  # Clauses deleted for lack of memory   : 0
% 0.19/0.45  # Backward-subsumed                    : 18
% 0.19/0.45  # Backward-rewritten                   : 8
% 0.19/0.45  # Generated clauses                    : 1407
% 0.19/0.45  # ...of the previous two non-trivial   : 832
% 0.19/0.45  # Contextual simplify-reflections      : 30
% 0.19/0.45  # Paramodulations                      : 1398
% 0.19/0.45  # Factorizations                       : 0
% 0.19/0.45  # Equation resolutions                 : 9
% 0.19/0.45  # Propositional unsat checks           : 0
% 0.19/0.45  #    Propositional check models        : 0
% 0.19/0.45  #    Propositional check unsatisfiable : 0
% 0.19/0.45  #    Propositional clauses             : 0
% 0.19/0.45  #    Propositional clauses after purity: 0
% 0.19/0.45  #    Propositional unsat core size     : 0
% 0.19/0.45  #    Propositional preprocessing time  : 0.000
% 0.19/0.45  #    Propositional encoding time       : 0.000
% 0.19/0.45  #    Propositional solver time         : 0.000
% 0.19/0.45  #    Success case prop preproc time    : 0.000
% 0.19/0.45  #    Success case prop encoding time   : 0.000
% 0.19/0.45  #    Success case prop solver time     : 0.000
% 0.19/0.45  # Current number of processed clauses  : 444
% 0.19/0.45  #    Positive orientable unit clauses  : 196
% 0.19/0.45  #    Positive unorientable unit clauses: 0
% 0.19/0.45  #    Negative unit clauses             : 5
% 0.19/0.45  #    Non-unit-clauses                  : 243
% 0.19/0.45  # Current number of unprocessed clauses: 287
% 0.19/0.45  # ...number of literals in the above   : 1500
% 0.19/0.45  # Current number of archived formulas  : 0
% 0.19/0.45  # Current number of archived clauses   : 68
% 0.19/0.45  # Clause-clause subsumption calls (NU) : 8241
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 1782
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 129
% 0.19/0.45  # Unit Clause-clause subsumption calls : 128
% 0.19/0.45  # Rewrite failures with RHS unbound    : 0
% 0.19/0.45  # BW rewrite match attempts            : 920
% 0.19/0.45  # BW rewrite match successes           : 4
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 70436
% 0.19/0.45  
% 0.19/0.45  # -------------------------------------------------
% 0.19/0.45  # User time                : 0.104 s
% 0.19/0.45  # System time              : 0.006 s
% 0.19/0.45  # Total time               : 0.111 s
% 0.19/0.45  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
