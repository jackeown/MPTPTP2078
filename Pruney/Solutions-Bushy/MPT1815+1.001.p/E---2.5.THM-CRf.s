%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1815+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:49 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   95 (4742 expanded)
%              Number of clauses        :   84 (1355 expanded)
%              Number of leaves         :    4 (1173 expanded)
%              Depth                    :   12
%              Number of atoms          :  586 (156468 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   49 (   5 average)
%              Maximal clause size      :   91 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t129_tmap_1,axiom,(
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
                 => ( r4_tsep_1(X1,X3,X4)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                       => ( ( v1_funct_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)))
                            & v1_funct_2(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_tsep_1(X1,X3,X4),X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
                        <=> ( v1_funct_1(k2_tmap_1(X1,X2,X5,X3))
                            & v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X5,X3),X3,X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                            & v1_funct_1(k2_tmap_1(X1,X2,X5,X4))
                            & v1_funct_2(k2_tmap_1(X1,X2,X5,X4),u1_struct_0(X4),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X5,X4),X4,X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_tmap_1)).

fof(t131_tmap_1,conjecture,(
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
                  ( ( ~ v2_struct_0(X4)
                    & v1_tsep_1(X4,X1)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( ~ v2_struct_0(X5)
                        & v1_tsep_1(X5,X1)
                        & m1_pre_topc(X5,X1) )
                     => ( ( v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))
                          & v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))
                          & v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)
                          & m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2)))) )
                      <=> ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
                          & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
                          & v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
                          & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
                          & v1_funct_1(k2_tmap_1(X1,X2,X3,X5))
                          & v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))
                          & v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)
                          & m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_tmap_1)).

fof(t88_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_tsep_1(X2,X1)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( v1_tsep_1(X3,X1)
                & m1_pre_topc(X3,X1) )
             => r4_tsep_1(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tsep_1)).

fof(c_0_3,plain,(
    ! [X4,X1,X5,X3,X2] :
      ( epred1_5(X2,X3,X5,X4,X1)
    <=> ( ( v1_funct_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_tsep_1(X1,X3,X4),X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
      <=> ( v1_funct_1(k2_tmap_1(X1,X2,X5,X3))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,X3),X3,X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
          & v1_funct_1(k2_tmap_1(X1,X2,X5,X4))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,X4),u1_struct_0(X4),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,X4),X4,X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ),
    introduced(definition)).

fof(c_0_4,axiom,(
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
                 => ( r4_tsep_1(X1,X3,X4)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                       => epred1_5(X2,X3,X5,X4,X1) ) ) ) ) ) ) ),
    inference(apply_def,[status(thm)],[t129_tmap_1,c_0_3])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
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
                    ( ( ~ v2_struct_0(X4)
                      & v1_tsep_1(X4,X1)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( ~ v2_struct_0(X5)
                          & v1_tsep_1(X5,X1)
                          & m1_pre_topc(X5,X1) )
                       => ( ( v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))
                            & v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2)))) )
                        <=> ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
                            & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
                            & v1_funct_1(k2_tmap_1(X1,X2,X3,X5))
                            & v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t131_tmap_1])).

fof(c_0_6,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X8,X6)
      | v2_struct_0(X9)
      | ~ m1_pre_topc(X9,X6)
      | ~ r4_tsep_1(X6,X8,X9)
      | ~ v1_funct_1(X10)
      | ~ v1_funct_2(X10,u1_struct_0(X6),u1_struct_0(X7))
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | epred1_5(X7,X8,X10,X9,X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & ~ v2_struct_0(esk4_0)
    & v1_tsep_1(esk4_0,esk1_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & ~ v2_struct_0(esk5_0)
    & v1_tsep_1(esk5_0,esk1_0)
    & m1_pre_topc(esk5_0,esk1_0)
    & ( ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)))
      | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0))
      | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0)
      | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0))))
      | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
      | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
      | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
      | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
      | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).

fof(c_0_8,plain,(
    ! [X11,X12,X13] :
      ( v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ v1_tsep_1(X12,X11)
      | ~ m1_pre_topc(X12,X11)
      | ~ v1_tsep_1(X13,X11)
      | ~ m1_pre_topc(X13,X11)
      | r4_tsep_1(X11,X12,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t88_tsep_1])])])])).

cnf(c_0_9,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | epred1_5(X2,X3,X5,X4,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ r4_tsep_1(X1,X3,X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | r4_tsep_1(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v1_tsep_1(X3,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_22,plain,(
    ! [X4,X1,X5,X3,X2] :
      ( epred1_5(X2,X3,X5,X4,X1)
     => ( ( v1_funct_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_tsep_1(X1,X3,X4),X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
      <=> ( v1_funct_1(k2_tmap_1(X1,X2,X5,X3))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,X3),X3,X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
          & v1_funct_1(k2_tmap_1(X1,X2,X5,X4))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,X4),u1_struct_0(X4),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,X4),X4,X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_3])).

cnf(c_0_23,negated_conjecture,
    ( epred1_5(esk2_0,X1,esk3_0,X2,esk1_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r4_tsep_1(esk1_0,X1,X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17]),c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r4_tsep_1(esk1_0,X1,esk5_0)
    | ~ v1_tsep_1(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_14]),c_0_16])]),c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_26,plain,(
    ! [X19,X20,X21,X22,X23] :
      ( ( v1_funct_1(k2_tmap_1(X20,X23,X21,X22))
        | ~ v1_funct_1(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)))
        | ~ v1_funct_2(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),u1_struct_0(k1_tsep_1(X20,X22,X19)),u1_struct_0(X23))
        | ~ v5_pre_topc(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),k1_tsep_1(X20,X22,X19),X23)
        | ~ m1_subset_1(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X20,X22,X19)),u1_struct_0(X23))))
        | ~ epred1_5(X23,X22,X21,X19,X20) )
      & ( v1_funct_2(k2_tmap_1(X20,X23,X21,X22),u1_struct_0(X22),u1_struct_0(X23))
        | ~ v1_funct_1(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)))
        | ~ v1_funct_2(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),u1_struct_0(k1_tsep_1(X20,X22,X19)),u1_struct_0(X23))
        | ~ v5_pre_topc(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),k1_tsep_1(X20,X22,X19),X23)
        | ~ m1_subset_1(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X20,X22,X19)),u1_struct_0(X23))))
        | ~ epred1_5(X23,X22,X21,X19,X20) )
      & ( v5_pre_topc(k2_tmap_1(X20,X23,X21,X22),X22,X23)
        | ~ v1_funct_1(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)))
        | ~ v1_funct_2(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),u1_struct_0(k1_tsep_1(X20,X22,X19)),u1_struct_0(X23))
        | ~ v5_pre_topc(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),k1_tsep_1(X20,X22,X19),X23)
        | ~ m1_subset_1(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X20,X22,X19)),u1_struct_0(X23))))
        | ~ epred1_5(X23,X22,X21,X19,X20) )
      & ( m1_subset_1(k2_tmap_1(X20,X23,X21,X22),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X23))))
        | ~ v1_funct_1(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)))
        | ~ v1_funct_2(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),u1_struct_0(k1_tsep_1(X20,X22,X19)),u1_struct_0(X23))
        | ~ v5_pre_topc(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),k1_tsep_1(X20,X22,X19),X23)
        | ~ m1_subset_1(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X20,X22,X19)),u1_struct_0(X23))))
        | ~ epred1_5(X23,X22,X21,X19,X20) )
      & ( v1_funct_1(k2_tmap_1(X20,X23,X21,X19))
        | ~ v1_funct_1(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)))
        | ~ v1_funct_2(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),u1_struct_0(k1_tsep_1(X20,X22,X19)),u1_struct_0(X23))
        | ~ v5_pre_topc(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),k1_tsep_1(X20,X22,X19),X23)
        | ~ m1_subset_1(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X20,X22,X19)),u1_struct_0(X23))))
        | ~ epred1_5(X23,X22,X21,X19,X20) )
      & ( v1_funct_2(k2_tmap_1(X20,X23,X21,X19),u1_struct_0(X19),u1_struct_0(X23))
        | ~ v1_funct_1(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)))
        | ~ v1_funct_2(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),u1_struct_0(k1_tsep_1(X20,X22,X19)),u1_struct_0(X23))
        | ~ v5_pre_topc(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),k1_tsep_1(X20,X22,X19),X23)
        | ~ m1_subset_1(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X20,X22,X19)),u1_struct_0(X23))))
        | ~ epred1_5(X23,X22,X21,X19,X20) )
      & ( v5_pre_topc(k2_tmap_1(X20,X23,X21,X19),X19,X23)
        | ~ v1_funct_1(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)))
        | ~ v1_funct_2(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),u1_struct_0(k1_tsep_1(X20,X22,X19)),u1_struct_0(X23))
        | ~ v5_pre_topc(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),k1_tsep_1(X20,X22,X19),X23)
        | ~ m1_subset_1(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X20,X22,X19)),u1_struct_0(X23))))
        | ~ epred1_5(X23,X22,X21,X19,X20) )
      & ( m1_subset_1(k2_tmap_1(X20,X23,X21,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X23))))
        | ~ v1_funct_1(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)))
        | ~ v1_funct_2(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),u1_struct_0(k1_tsep_1(X20,X22,X19)),u1_struct_0(X23))
        | ~ v5_pre_topc(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),k1_tsep_1(X20,X22,X19),X23)
        | ~ m1_subset_1(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X20,X22,X19)),u1_struct_0(X23))))
        | ~ epred1_5(X23,X22,X21,X19,X20) )
      & ( v1_funct_1(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)))
        | ~ v1_funct_1(k2_tmap_1(X20,X23,X21,X22))
        | ~ v1_funct_2(k2_tmap_1(X20,X23,X21,X22),u1_struct_0(X22),u1_struct_0(X23))
        | ~ v5_pre_topc(k2_tmap_1(X20,X23,X21,X22),X22,X23)
        | ~ m1_subset_1(k2_tmap_1(X20,X23,X21,X22),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X23))))
        | ~ v1_funct_1(k2_tmap_1(X20,X23,X21,X19))
        | ~ v1_funct_2(k2_tmap_1(X20,X23,X21,X19),u1_struct_0(X19),u1_struct_0(X23))
        | ~ v5_pre_topc(k2_tmap_1(X20,X23,X21,X19),X19,X23)
        | ~ m1_subset_1(k2_tmap_1(X20,X23,X21,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X23))))
        | ~ epred1_5(X23,X22,X21,X19,X20) )
      & ( v1_funct_2(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),u1_struct_0(k1_tsep_1(X20,X22,X19)),u1_struct_0(X23))
        | ~ v1_funct_1(k2_tmap_1(X20,X23,X21,X22))
        | ~ v1_funct_2(k2_tmap_1(X20,X23,X21,X22),u1_struct_0(X22),u1_struct_0(X23))
        | ~ v5_pre_topc(k2_tmap_1(X20,X23,X21,X22),X22,X23)
        | ~ m1_subset_1(k2_tmap_1(X20,X23,X21,X22),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X23))))
        | ~ v1_funct_1(k2_tmap_1(X20,X23,X21,X19))
        | ~ v1_funct_2(k2_tmap_1(X20,X23,X21,X19),u1_struct_0(X19),u1_struct_0(X23))
        | ~ v5_pre_topc(k2_tmap_1(X20,X23,X21,X19),X19,X23)
        | ~ m1_subset_1(k2_tmap_1(X20,X23,X21,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X23))))
        | ~ epred1_5(X23,X22,X21,X19,X20) )
      & ( v5_pre_topc(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),k1_tsep_1(X20,X22,X19),X23)
        | ~ v1_funct_1(k2_tmap_1(X20,X23,X21,X22))
        | ~ v1_funct_2(k2_tmap_1(X20,X23,X21,X22),u1_struct_0(X22),u1_struct_0(X23))
        | ~ v5_pre_topc(k2_tmap_1(X20,X23,X21,X22),X22,X23)
        | ~ m1_subset_1(k2_tmap_1(X20,X23,X21,X22),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X23))))
        | ~ v1_funct_1(k2_tmap_1(X20,X23,X21,X19))
        | ~ v1_funct_2(k2_tmap_1(X20,X23,X21,X19),u1_struct_0(X19),u1_struct_0(X23))
        | ~ v5_pre_topc(k2_tmap_1(X20,X23,X21,X19),X19,X23)
        | ~ m1_subset_1(k2_tmap_1(X20,X23,X21,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X23))))
        | ~ epred1_5(X23,X22,X21,X19,X20) )
      & ( m1_subset_1(k2_tmap_1(X20,X23,X21,k1_tsep_1(X20,X22,X19)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X20,X22,X19)),u1_struct_0(X23))))
        | ~ v1_funct_1(k2_tmap_1(X20,X23,X21,X22))
        | ~ v1_funct_2(k2_tmap_1(X20,X23,X21,X22),u1_struct_0(X22),u1_struct_0(X23))
        | ~ v5_pre_topc(k2_tmap_1(X20,X23,X21,X22),X22,X23)
        | ~ m1_subset_1(k2_tmap_1(X20,X23,X21,X22),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X23))))
        | ~ v1_funct_1(k2_tmap_1(X20,X23,X21,X19))
        | ~ v1_funct_2(k2_tmap_1(X20,X23,X21,X19),u1_struct_0(X19),u1_struct_0(X23))
        | ~ v5_pre_topc(k2_tmap_1(X20,X23,X21,X19),X19,X23)
        | ~ m1_subset_1(k2_tmap_1(X20,X23,X21,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X23))))
        | ~ epred1_5(X23,X22,X21,X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

cnf(c_0_27,negated_conjecture,
    ( epred1_5(esk2_0,X1,esk3_0,esk5_0,esk1_0)
    | v2_struct_0(X1)
    | ~ v1_tsep_1(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_21])]),c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X4,X3,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_33,negated_conjecture,
    ( epred1_5(esk2_0,esk4_0,esk3_0,esk5_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_35,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_36,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_37,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_tsep_1(X1,X5,X4),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X5,X3,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_39,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_40,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_41,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_42,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X4,X3,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_47,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_tsep_1(X1,X5,X4),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X5,X3,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_52,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X4,X3,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_57,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_tsep_1(X1,X5,X4),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X5,X3,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_62,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X4,X3,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
    | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
    | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_65,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
    | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
    | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_67,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_tsep_1(X1,X5,X4),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X5,X3,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_68,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
    | m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_69,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
    | v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_70,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
    | v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
    | v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_72,negated_conjecture,
    ( ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0))
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0))))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_73,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_74,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_33])]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_33])]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_33])]),c_0_49]),c_0_50]),c_0_51])).

cnf(c_0_77,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_33])]),c_0_54]),c_0_55]),c_0_56])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_33])]),c_0_59]),c_0_60]),c_0_61])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_33])]),c_0_64]),c_0_65]),c_0_66])).

cnf(c_0_80,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_33])]),c_0_69]),c_0_70]),c_0_71])).

cnf(c_0_81,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X5))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))
    | ~ epred1_5(X2,X4,X3,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_82,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_75]),c_0_76]),c_0_77]),c_0_78]),c_0_79]),c_0_80])])).

cnf(c_0_83,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X5))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))
    | ~ epred1_5(X2,X4,X3,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_84,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,esk5_0)))
    | ~ epred1_5(esk2_0,X1,esk3_0,esk5_0,esk1_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X1,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_76]),c_0_74]),c_0_78]),c_0_80])])).

cnf(c_0_85,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X5))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))
    | ~ epred1_5(X2,X4,X3,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_86,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_33]),c_0_74]),c_0_73]),c_0_76]),c_0_75]),c_0_78]),c_0_77]),c_0_80]),c_0_79])])).

cnf(c_0_87,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_75]),c_0_33]),c_0_73]),c_0_77]),c_0_79])])).

cnf(c_0_88,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,esk5_0)),k1_tsep_1(esk1_0,X1,esk5_0),esk2_0)
    | ~ epred1_5(esk2_0,X1,esk3_0,esk5_0,esk1_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X1,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_76]),c_0_74]),c_0_78]),c_0_80])])).

cnf(c_0_89,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X5))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))
    | ~ epred1_5(X2,X4,X3,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_90,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87])])).

cnf(c_0_91,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),k1_tsep_1(esk1_0,esk4_0,esk5_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_75]),c_0_33]),c_0_73]),c_0_77]),c_0_79])])).

cnf(c_0_92,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,X1,esk5_0)),u1_struct_0(esk2_0))
    | ~ epred1_5(esk2_0,X1,esk3_0,esk5_0,esk1_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X1,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_76]),c_0_74]),c_0_78]),c_0_80])])).

cnf(c_0_93,negated_conjecture,
    ( ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(k1_tsep_1(esk1_0,esk4_0,esk5_0)),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91])])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_75]),c_0_33]),c_0_73]),c_0_77]),c_0_79])]),c_0_93]),
    [proof]).

%------------------------------------------------------------------------------
