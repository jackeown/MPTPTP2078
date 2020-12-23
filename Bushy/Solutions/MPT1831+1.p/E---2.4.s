%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t147_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:09 EDT 2019

% Result     : Theorem 277.63s
% Output     : CNFRefutation 277.63s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 936 expanded)
%              Number of clauses        :   58 ( 258 expanded)
%              Number of leaves         :    9 ( 236 expanded)
%              Depth                    :   13
%              Number of atoms          :  815 (18299 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   28 (   9 average)
%              Maximal clause size      :   88 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t147_tmap_1.p',redefinition_r2_funct_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t147_tmap_1.p',t3_subset)).

fof(t147_tmap_1,conjecture,(
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
                & v1_tsep_1(X3,X1)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & v1_tsep_1(X4,X1)
                    & m1_pre_topc(X4,X1) )
                 => ( ~ r1_tsep_1(X3,X4)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                          & v5_pre_topc(X5,X3,X2)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
                              & v5_pre_topc(X6,X4,X2)
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                           => ( r2_funct_2(u1_struct_0(k2_tsep_1(X1,X3,X4)),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,k2_tsep_1(X1,X3,X4),X5),k3_tmap_1(X1,X2,X4,k2_tsep_1(X1,X3,X4),X6))
                             => ( v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))
                                & v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                                & v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2)
                                & m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t147_tmap_1.p',t147_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t147_tmap_1.p',dt_k3_tmap_1)).

fof(t140_tmap_1,axiom,(
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
                 => ( ~ r1_tsep_1(X3,X4)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                           => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,k10_tmap_1(X1,X2,X3,X4,X5,X6)),X5)
                                & r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,k10_tmap_1(X1,X2,X3,X4,X5,X6)),X6) )
                            <=> r2_funct_2(u1_struct_0(k2_tsep_1(X1,X3,X4)),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,k2_tsep_1(X1,X3,X4),X5),k3_tmap_1(X1,X2,X4,k2_tsep_1(X1,X3,X4),X6)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t147_tmap_1.p',t140_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t147_tmap_1.p',dt_k10_tmap_1)).

fof(t128_tmap_1,axiom,(
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
                & v1_tsep_1(X3,X1)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & v1_tsep_1(X4,X1)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
                     => ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                          & v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
                      <=> ( v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))
                          & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2))
                          & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2)
                          & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                          & v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5))
                          & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2))
                          & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2)
                          & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t147_tmap_1.p',t128_tmap_1)).

fof(dt_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
        & v1_pre_topc(k1_tsep_1(X1,X2,X3))
        & m1_pre_topc(k1_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t147_tmap_1.p',dt_k1_tsep_1)).

fof(c_0_8,plain,(
    ! [X52,X53,X54,X55] :
      ( ( ~ r2_funct_2(X52,X53,X54,X55)
        | X54 = X55
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X52,X53)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X52,X53)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( X54 != X55
        | r2_funct_2(X52,X53,X54,X55)
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X52,X53)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X52,X53)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

fof(c_0_9,plain,(
    ! [X81,X82] :
      ( ( ~ m1_subset_1(X81,k1_zfmisc_1(X82))
        | r1_tarski(X81,X82) )
      & ( ~ r1_tarski(X81,X82)
        | m1_subset_1(X81,k1_zfmisc_1(X82)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_10,negated_conjecture,(
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
                  & v1_tsep_1(X3,X1)
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & v1_tsep_1(X4,X1)
                      & m1_pre_topc(X4,X1) )
                   => ( ~ r1_tsep_1(X3,X4)
                     => ! [X5] :
                          ( ( v1_funct_1(X5)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                            & v5_pre_topc(X5,X3,X2)
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                         => ! [X6] :
                              ( ( v1_funct_1(X6)
                                & v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
                                & v5_pre_topc(X6,X4,X2)
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                             => ( r2_funct_2(u1_struct_0(k2_tsep_1(X1,X3,X4)),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,k2_tsep_1(X1,X3,X4),X5),k3_tmap_1(X1,X2,X4,k2_tsep_1(X1,X3,X4),X6))
                               => ( v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))
                                  & v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                                  & v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2)
                                  & m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t147_tmap_1])).

fof(c_0_11,plain,(
    ! [X5,X4,X3,X2,X1] :
      ( epred1_5(X1,X2,X3,X4,X5)
    <=> ( ( v1_funct_1(X5)
          & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
          & v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
      <=> ( v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))
          & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2))
          & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2)
          & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
          & v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5))
          & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2))
          & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2)
          & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ),
    introduced(definition)).

cnf(c_0_12,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X33,X34,X35,X36,X37] :
      ( ( v1_funct_1(k3_tmap_1(X33,X34,X35,X36,X37))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_pre_topc(X35,X33)
        | ~ m1_pre_topc(X36,X33)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,u1_struct_0(X35),u1_struct_0(X34))
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X34)))) )
      & ( v1_funct_2(k3_tmap_1(X33,X34,X35,X36,X37),u1_struct_0(X36),u1_struct_0(X34))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_pre_topc(X35,X33)
        | ~ m1_pre_topc(X36,X33)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,u1_struct_0(X35),u1_struct_0(X34))
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X34)))) )
      & ( m1_subset_1(k3_tmap_1(X33,X34,X35,X36,X37),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X34))))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_pre_topc(X35,X33)
        | ~ m1_pre_topc(X36,X33)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,u1_struct_0(X35),u1_struct_0(X34))
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X34)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).

fof(c_0_15,plain,(
    ! [X71,X72,X73,X74,X75,X76] :
      ( ( ~ r2_funct_2(u1_struct_0(X73),u1_struct_0(X72),k3_tmap_1(X71,X72,k1_tsep_1(X71,X73,X74),X73,k10_tmap_1(X71,X72,X73,X74,X75,X76)),X75)
        | ~ r2_funct_2(u1_struct_0(X74),u1_struct_0(X72),k3_tmap_1(X71,X72,k1_tsep_1(X71,X73,X74),X74,k10_tmap_1(X71,X72,X73,X74,X75,X76)),X76)
        | r2_funct_2(u1_struct_0(k2_tsep_1(X71,X73,X74)),u1_struct_0(X72),k3_tmap_1(X71,X72,X73,k2_tsep_1(X71,X73,X74),X75),k3_tmap_1(X71,X72,X74,k2_tsep_1(X71,X73,X74),X76))
        | ~ v1_funct_1(X76)
        | ~ v1_funct_2(X76,u1_struct_0(X74),u1_struct_0(X72))
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X74),u1_struct_0(X72))))
        | ~ v1_funct_1(X75)
        | ~ v1_funct_2(X75,u1_struct_0(X73),u1_struct_0(X72))
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X73),u1_struct_0(X72))))
        | r1_tsep_1(X73,X74)
        | v2_struct_0(X74)
        | ~ m1_pre_topc(X74,X71)
        | v2_struct_0(X73)
        | ~ m1_pre_topc(X73,X71)
        | v2_struct_0(X72)
        | ~ v2_pre_topc(X72)
        | ~ l1_pre_topc(X72)
        | v2_struct_0(X71)
        | ~ v2_pre_topc(X71)
        | ~ l1_pre_topc(X71) )
      & ( r2_funct_2(u1_struct_0(X73),u1_struct_0(X72),k3_tmap_1(X71,X72,k1_tsep_1(X71,X73,X74),X73,k10_tmap_1(X71,X72,X73,X74,X75,X76)),X75)
        | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X71,X73,X74)),u1_struct_0(X72),k3_tmap_1(X71,X72,X73,k2_tsep_1(X71,X73,X74),X75),k3_tmap_1(X71,X72,X74,k2_tsep_1(X71,X73,X74),X76))
        | ~ v1_funct_1(X76)
        | ~ v1_funct_2(X76,u1_struct_0(X74),u1_struct_0(X72))
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X74),u1_struct_0(X72))))
        | ~ v1_funct_1(X75)
        | ~ v1_funct_2(X75,u1_struct_0(X73),u1_struct_0(X72))
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X73),u1_struct_0(X72))))
        | r1_tsep_1(X73,X74)
        | v2_struct_0(X74)
        | ~ m1_pre_topc(X74,X71)
        | v2_struct_0(X73)
        | ~ m1_pre_topc(X73,X71)
        | v2_struct_0(X72)
        | ~ v2_pre_topc(X72)
        | ~ l1_pre_topc(X72)
        | v2_struct_0(X71)
        | ~ v2_pre_topc(X71)
        | ~ l1_pre_topc(X71) )
      & ( r2_funct_2(u1_struct_0(X74),u1_struct_0(X72),k3_tmap_1(X71,X72,k1_tsep_1(X71,X73,X74),X74,k10_tmap_1(X71,X72,X73,X74,X75,X76)),X76)
        | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X71,X73,X74)),u1_struct_0(X72),k3_tmap_1(X71,X72,X73,k2_tsep_1(X71,X73,X74),X75),k3_tmap_1(X71,X72,X74,k2_tsep_1(X71,X73,X74),X76))
        | ~ v1_funct_1(X76)
        | ~ v1_funct_2(X76,u1_struct_0(X74),u1_struct_0(X72))
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X74),u1_struct_0(X72))))
        | ~ v1_funct_1(X75)
        | ~ v1_funct_2(X75,u1_struct_0(X73),u1_struct_0(X72))
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X73),u1_struct_0(X72))))
        | r1_tsep_1(X73,X74)
        | v2_struct_0(X74)
        | ~ m1_pre_topc(X74,X71)
        | v2_struct_0(X73)
        | ~ m1_pre_topc(X73,X71)
        | v2_struct_0(X72)
        | ~ v2_pre_topc(X72)
        | ~ l1_pre_topc(X72)
        | v2_struct_0(X71)
        | ~ v2_pre_topc(X71)
        | ~ l1_pre_topc(X71) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t140_tmap_1])])])])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v1_tsep_1(esk3_0,esk1_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & v1_tsep_1(esk4_0,esk1_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & ~ r1_tsep_1(esk3_0,esk4_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    & v5_pre_topc(esk5_0,esk3_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    & v5_pre_topc(esk6_0,esk4_0,esk2_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    & r2_funct_2(u1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk5_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk6_0))
    & ( ~ v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
      | ~ v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))
      | ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)
      | ~ m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0)))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_17,plain,(
    ! [X5,X4,X3,X2,X1] :
      ( epred1_5(X1,X2,X3,X4,X5)
     => ( ( v1_funct_1(X5)
          & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
          & v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
      <=> ( v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))
          & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2))
          & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2)
          & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
          & v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5))
          & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2))
          & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2)
          & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( X1 = X2
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,X4))
    | ~ r2_funct_2(X3,X4,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_2(X2,X3,X4)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X1,k10_tmap_1(X3,X2,X1,X4,X5,X6)),X5)
    | r1_tsep_1(X1,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X3,X1,X4)),u1_struct_0(X2),k3_tmap_1(X3,X2,X1,k2_tsep_1(X3,X1,X4),X5),k3_tmap_1(X3,X2,X4,k2_tsep_1(X3,X1,X4),X6))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk5_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,k2_tsep_1(esk1_0,esk3_0,esk4_0),esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tsep_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_42,plain,(
    ! [X21,X22,X23,X24,X25,X26] :
      ( ( v1_funct_1(k10_tmap_1(X21,X22,X23,X24,X25,X26))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X21)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X22))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X22))))
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(X22))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X22)))) )
      & ( v1_funct_2(k10_tmap_1(X21,X22,X23,X24,X25,X26),u1_struct_0(k1_tsep_1(X21,X23,X24)),u1_struct_0(X22))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X21)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X22))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X22))))
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(X22))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X22)))) )
      & ( m1_subset_1(k10_tmap_1(X21,X22,X23,X24,X25,X26),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X21,X23,X24)),u1_struct_0(X22))))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21)
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X21)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X22))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X22))))
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(X22))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X22)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_tmap_1])])])])).

fof(c_0_43,plain,(
    ! [X101,X102,X103,X104,X105] :
      ( ( v1_funct_1(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X103,X101))
        | ~ v1_funct_1(X101)
        | ~ v1_funct_2(X101,u1_struct_0(k1_tsep_1(X105,X103,X102)),u1_struct_0(X104))
        | ~ v5_pre_topc(X101,k1_tsep_1(X105,X103,X102),X104)
        | ~ m1_subset_1(X101,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X105,X103,X102)),u1_struct_0(X104))))
        | ~ epred1_5(X105,X104,X103,X102,X101) )
      & ( v1_funct_2(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X103,X101),u1_struct_0(X103),u1_struct_0(X104))
        | ~ v1_funct_1(X101)
        | ~ v1_funct_2(X101,u1_struct_0(k1_tsep_1(X105,X103,X102)),u1_struct_0(X104))
        | ~ v5_pre_topc(X101,k1_tsep_1(X105,X103,X102),X104)
        | ~ m1_subset_1(X101,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X105,X103,X102)),u1_struct_0(X104))))
        | ~ epred1_5(X105,X104,X103,X102,X101) )
      & ( v5_pre_topc(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X103,X101),X103,X104)
        | ~ v1_funct_1(X101)
        | ~ v1_funct_2(X101,u1_struct_0(k1_tsep_1(X105,X103,X102)),u1_struct_0(X104))
        | ~ v5_pre_topc(X101,k1_tsep_1(X105,X103,X102),X104)
        | ~ m1_subset_1(X101,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X105,X103,X102)),u1_struct_0(X104))))
        | ~ epred1_5(X105,X104,X103,X102,X101) )
      & ( m1_subset_1(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X103,X101),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X103),u1_struct_0(X104))))
        | ~ v1_funct_1(X101)
        | ~ v1_funct_2(X101,u1_struct_0(k1_tsep_1(X105,X103,X102)),u1_struct_0(X104))
        | ~ v5_pre_topc(X101,k1_tsep_1(X105,X103,X102),X104)
        | ~ m1_subset_1(X101,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X105,X103,X102)),u1_struct_0(X104))))
        | ~ epred1_5(X105,X104,X103,X102,X101) )
      & ( v1_funct_1(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X102,X101))
        | ~ v1_funct_1(X101)
        | ~ v1_funct_2(X101,u1_struct_0(k1_tsep_1(X105,X103,X102)),u1_struct_0(X104))
        | ~ v5_pre_topc(X101,k1_tsep_1(X105,X103,X102),X104)
        | ~ m1_subset_1(X101,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X105,X103,X102)),u1_struct_0(X104))))
        | ~ epred1_5(X105,X104,X103,X102,X101) )
      & ( v1_funct_2(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X102,X101),u1_struct_0(X102),u1_struct_0(X104))
        | ~ v1_funct_1(X101)
        | ~ v1_funct_2(X101,u1_struct_0(k1_tsep_1(X105,X103,X102)),u1_struct_0(X104))
        | ~ v5_pre_topc(X101,k1_tsep_1(X105,X103,X102),X104)
        | ~ m1_subset_1(X101,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X105,X103,X102)),u1_struct_0(X104))))
        | ~ epred1_5(X105,X104,X103,X102,X101) )
      & ( v5_pre_topc(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X102,X101),X102,X104)
        | ~ v1_funct_1(X101)
        | ~ v1_funct_2(X101,u1_struct_0(k1_tsep_1(X105,X103,X102)),u1_struct_0(X104))
        | ~ v5_pre_topc(X101,k1_tsep_1(X105,X103,X102),X104)
        | ~ m1_subset_1(X101,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X105,X103,X102)),u1_struct_0(X104))))
        | ~ epred1_5(X105,X104,X103,X102,X101) )
      & ( m1_subset_1(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X102,X101),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X102),u1_struct_0(X104))))
        | ~ v1_funct_1(X101)
        | ~ v1_funct_2(X101,u1_struct_0(k1_tsep_1(X105,X103,X102)),u1_struct_0(X104))
        | ~ v5_pre_topc(X101,k1_tsep_1(X105,X103,X102),X104)
        | ~ m1_subset_1(X101,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X105,X103,X102)),u1_struct_0(X104))))
        | ~ epred1_5(X105,X104,X103,X102,X101) )
      & ( v1_funct_1(X101)
        | ~ v1_funct_1(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X103,X101))
        | ~ v1_funct_2(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X103,X101),u1_struct_0(X103),u1_struct_0(X104))
        | ~ v5_pre_topc(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X103,X101),X103,X104)
        | ~ m1_subset_1(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X103,X101),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X103),u1_struct_0(X104))))
        | ~ v1_funct_1(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X102,X101))
        | ~ v1_funct_2(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X102,X101),u1_struct_0(X102),u1_struct_0(X104))
        | ~ v5_pre_topc(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X102,X101),X102,X104)
        | ~ m1_subset_1(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X102,X101),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X102),u1_struct_0(X104))))
        | ~ epred1_5(X105,X104,X103,X102,X101) )
      & ( v1_funct_2(X101,u1_struct_0(k1_tsep_1(X105,X103,X102)),u1_struct_0(X104))
        | ~ v1_funct_1(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X103,X101))
        | ~ v1_funct_2(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X103,X101),u1_struct_0(X103),u1_struct_0(X104))
        | ~ v5_pre_topc(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X103,X101),X103,X104)
        | ~ m1_subset_1(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X103,X101),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X103),u1_struct_0(X104))))
        | ~ v1_funct_1(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X102,X101))
        | ~ v1_funct_2(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X102,X101),u1_struct_0(X102),u1_struct_0(X104))
        | ~ v5_pre_topc(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X102,X101),X102,X104)
        | ~ m1_subset_1(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X102,X101),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X102),u1_struct_0(X104))))
        | ~ epred1_5(X105,X104,X103,X102,X101) )
      & ( v5_pre_topc(X101,k1_tsep_1(X105,X103,X102),X104)
        | ~ v1_funct_1(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X103,X101))
        | ~ v1_funct_2(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X103,X101),u1_struct_0(X103),u1_struct_0(X104))
        | ~ v5_pre_topc(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X103,X101),X103,X104)
        | ~ m1_subset_1(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X103,X101),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X103),u1_struct_0(X104))))
        | ~ v1_funct_1(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X102,X101))
        | ~ v1_funct_2(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X102,X101),u1_struct_0(X102),u1_struct_0(X104))
        | ~ v5_pre_topc(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X102,X101),X102,X104)
        | ~ m1_subset_1(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X102,X101),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X102),u1_struct_0(X104))))
        | ~ epred1_5(X105,X104,X103,X102,X101) )
      & ( m1_subset_1(X101,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X105,X103,X102)),u1_struct_0(X104))))
        | ~ v1_funct_1(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X103,X101))
        | ~ v1_funct_2(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X103,X101),u1_struct_0(X103),u1_struct_0(X104))
        | ~ v5_pre_topc(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X103,X101),X103,X104)
        | ~ m1_subset_1(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X103,X101),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X103),u1_struct_0(X104))))
        | ~ v1_funct_1(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X102,X101))
        | ~ v1_funct_2(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X102,X101),u1_struct_0(X102),u1_struct_0(X104))
        | ~ v5_pre_topc(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X102,X101),X102,X104)
        | ~ m1_subset_1(k3_tmap_1(X105,X104,k1_tsep_1(X105,X103,X102),X102,X101),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X102),u1_struct_0(X104))))
        | ~ epred1_5(X105,X104,X103,X102,X101) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_44,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = X6
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tarski(X6,k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))
    | ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,X4,X5),X6)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_45,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_25])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | ~ v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))
    | ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_48,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k3_tmap_1(X3,X2,k1_tsep_1(X3,X4,X1),X1,k10_tmap_1(X3,X2,X4,X1,X5,X6)),X6)
    | r1_tsep_1(X4,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X3,X4,X1)),u1_struct_0(X2),k3_tmap_1(X3,X2,X4,k2_tsep_1(X3,X4,X1),X5),k3_tmap_1(X3,X2,X1,k2_tsep_1(X3,X4,X1),X6))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_50,plain,
    ( v5_pre_topc(X1,k1_tsep_1(X2,X3,X4),X5)
    | ~ v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1))
    | ~ v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),u1_struct_0(X3),u1_struct_0(X5))
    | ~ v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),X3,X5)
    | ~ m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X5))))
    | ~ v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1))
    | ~ v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),u1_struct_0(X4),u1_struct_0(X5))
    | ~ v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),X4,X5)
    | ~ m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
    | ~ epred1_5(X2,X5,X3,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) = esk5_0
    | ~ m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk4_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_27]),c_0_29]),c_0_31]),c_0_33]),c_0_32]),c_0_35]),c_0_34])]),c_0_38]),c_0_39])).

cnf(c_0_52,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_33]),c_0_32]),c_0_35]),c_0_34])]),c_0_39]),c_0_38]),c_0_37]),c_0_40])).

cnf(c_0_53,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_31]),c_0_30]),c_0_32]),c_0_33]),c_0_34]),c_0_35])]),c_0_36]),c_0_40]),c_0_38]),c_0_39]),c_0_37])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk6_0,k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_24])).

cnf(c_0_56,plain,
    ( v5_pre_topc(X1,k1_tsep_1(X2,X3,X4),X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | ~ epred1_5(X2,X5,X3,X4,X1)
    | ~ m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X5))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X3,X4)),u1_struct_0(X5))))
    | ~ v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),X4,X5)
    | ~ v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),X3,X5)
    | ~ v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),u1_struct_0(X3),u1_struct_0(X5))
    | ~ v1_funct_2(X1,u1_struct_0(k1_tsep_1(X2,X3,X4)),u1_struct_0(X5))
    | ~ v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1))
    | ~ v1_funct_1(X1)
    | ~ m1_pre_topc(k1_tsep_1(X2,X3,X4),X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) = esk5_0
    | ~ v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk4_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_48]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_33]),c_0_32]),c_0_35]),c_0_34])]),c_0_39]),c_0_38]),c_0_37]),c_0_40])).

cnf(c_0_58,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_59,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_33]),c_0_32]),c_0_35]),c_0_34])]),c_0_39]),c_0_38]),c_0_37]),c_0_40])).

cnf(c_0_60,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) = esk6_0
    | ~ m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk4_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_54]),c_0_55]),c_0_26]),c_0_28]),c_0_30]),c_0_33]),c_0_32]),c_0_35]),c_0_34])]),c_0_38]),c_0_39])).

cnf(c_0_61,negated_conjecture,
    ( ~ epred1_5(esk1_0,esk2_0,esk3_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | ~ m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))))
    | ~ v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk4_0,esk2_0)
    | ~ v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk4_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_25]),c_0_58]),c_0_27]),c_0_29]),c_0_30]),c_0_33]),c_0_32]),c_0_35]),c_0_34])]),c_0_38]),c_0_39]),c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) = esk6_0
    | ~ v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk4_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_48]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_33]),c_0_32]),c_0_35]),c_0_34])]),c_0_39]),c_0_38]),c_0_37]),c_0_40])).

cnf(c_0_63,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_64,axiom,(
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
                & v1_tsep_1(X3,X1)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & v1_tsep_1(X4,X1)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
                     => epred1_5(X1,X2,X3,X4,X5) ) ) ) ) ) ),
    inference(apply_def,[status(thm)],[t128_tmap_1,c_0_11])).

cnf(c_0_65,negated_conjecture,
    ( ~ epred1_5(esk1_0,esk2_0,esk3_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | ~ m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk4_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])])).

fof(c_0_66,plain,(
    ! [X66,X67,X68,X69,X70] :
      ( v2_struct_0(X66)
      | ~ v2_pre_topc(X66)
      | ~ l1_pre_topc(X66)
      | v2_struct_0(X67)
      | ~ v2_pre_topc(X67)
      | ~ l1_pre_topc(X67)
      | v2_struct_0(X68)
      | ~ v1_tsep_1(X68,X66)
      | ~ m1_pre_topc(X68,X66)
      | v2_struct_0(X69)
      | ~ v1_tsep_1(X69,X66)
      | ~ m1_pre_topc(X69,X66)
      | ~ v1_funct_1(X70)
      | ~ v1_funct_2(X70,u1_struct_0(k1_tsep_1(X66,X68,X69)),u1_struct_0(X67))
      | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X66,X68,X69)),u1_struct_0(X67))))
      | epred1_5(X66,X67,X68,X69,X70) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_64])])])])).

cnf(c_0_67,negated_conjecture,
    ( ~ epred1_5(esk1_0,esk2_0,esk3_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | ~ v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk4_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_48]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_33]),c_0_32]),c_0_35]),c_0_34])]),c_0_39]),c_0_38]),c_0_37]),c_0_40])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | epred1_5(X1,X2,X3,X4,X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_tsep_1(X3,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_tsep_1(X4,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_69,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_70,negated_conjecture,
    ( ~ epred1_5(esk1_0,esk2_0,esk3_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | ~ v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk4_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_53]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_33]),c_0_32]),c_0_35]),c_0_34])]),c_0_39]),c_0_38]),c_0_37]),c_0_40])).

cnf(c_0_71,plain,
    ( epred1_5(X1,X2,X3,X4,k10_tmap_1(X1,X2,X3,X4,X5,X6))
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_tsep_1(X4,X1)
    | ~ v1_tsep_1(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_48]),c_0_69]),c_0_53])).

cnf(c_0_72,negated_conjecture,
    ( v1_tsep_1(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_73,negated_conjecture,
    ( v1_tsep_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_74,negated_conjecture,
    ( ~ v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | ~ m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk4_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_72]),c_0_73]),c_0_33]),c_0_32]),c_0_35]),c_0_34])]),c_0_40]),c_0_37]),c_0_38]),c_0_39])).

fof(c_0_75,plain,(
    ! [X27,X28,X29] :
      ( ( ~ v2_struct_0(k1_tsep_1(X27,X28,X29))
        | v2_struct_0(X27)
        | ~ l1_pre_topc(X27)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X27)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X27) )
      & ( v1_pre_topc(k1_tsep_1(X27,X28,X29))
        | v2_struct_0(X27)
        | ~ l1_pre_topc(X27)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X27)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X27) )
      & ( m1_pre_topc(k1_tsep_1(X27,X28,X29),X27)
        | v2_struct_0(X27)
        | ~ l1_pre_topc(X27)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X27)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

cnf(c_0_76,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(esk1_0,esk3_0,esk4_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_69]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_33]),c_0_32]),c_0_35]),c_0_34])]),c_0_39]),c_0_38]),c_0_37]),c_0_40])).

cnf(c_0_77,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_30]),c_0_31]),c_0_32])]),c_0_39]),c_0_37]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
