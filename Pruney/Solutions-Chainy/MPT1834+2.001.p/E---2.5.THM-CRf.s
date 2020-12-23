%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:36 EST 2020

% Result     : Theorem 0.62s
% Output     : CNFRefutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   95 (24280 expanded)
%              Number of clauses        :   80 (7070 expanded)
%              Number of leaves         :    7 (5946 expanded)
%              Depth                    :   23
%              Number of atoms          : 1342 (964234 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   40 (  10 average)
%              Maximal clause size      :  254 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t150_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r3_tsep_1(X1,X2,X3)
              <=> ( r1_tsep_1(X2,X3)
                  & ! [X4] :
                      ( ( ~ v2_struct_0(X4)
                        & v2_pre_topc(X4)
                        & l1_pre_topc(X4) )
                     => ! [X5] :
                          ( ( v1_funct_1(X5)
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X4))
                            & v5_pre_topc(X5,X2,X4)
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4)))) )
                         => ! [X6] :
                              ( ( v1_funct_1(X6)
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X4))
                                & v5_pre_topc(X6,X3,X4)
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))) )
                             => ( v1_funct_1(k10_tmap_1(X1,X4,X2,X3,X5,X6))
                                & v1_funct_2(k10_tmap_1(X1,X4,X2,X3,X5,X6),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))
                                & v5_pre_topc(k10_tmap_1(X1,X4,X2,X3,X5,X6),k1_tsep_1(X1,X2,X3),X4)
                                & m1_subset_1(k10_tmap_1(X1,X4,X2,X3,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_tmap_1)).

fof(t135_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r3_tsep_1(X1,X2,X3)
              <=> ( r1_tsep_1(X2,X3)
                  & ! [X4] :
                      ( ( ~ v2_struct_0(X4)
                        & v2_pre_topc(X4)
                        & l1_pre_topc(X4) )
                     => ! [X5] :
                          ( ( v1_funct_1(X5)
                            & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))) )
                         => ( ( v1_funct_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5))
                              & v1_funct_2(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5),u1_struct_0(X2),u1_struct_0(X4))
                              & v5_pre_topc(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5),X2,X4)
                              & m1_subset_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
                              & v1_funct_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5))
                              & v1_funct_2(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5),u1_struct_0(X3),u1_struct_0(X4))
                              & v5_pre_topc(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5),X3,X4)
                              & m1_subset_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))) )
                           => ( v1_funct_1(X5)
                              & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))
                              & v5_pre_topc(X5,k1_tsep_1(X1,X2,X3),X4)
                              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_tmap_1)).

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

fof(d13_tmap_1,axiom,(
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
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                         => ( ( r1_tsep_1(X3,X4)
                              | r2_funct_2(u1_struct_0(k2_tsep_1(X1,X3,X4)),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,k2_tsep_1(X1,X3,X4),X5),k3_tmap_1(X1,X2,X4,k2_tsep_1(X1,X3,X4),X6)) )
                           => ! [X7] :
                                ( ( v1_funct_1(X7)
                                  & v1_funct_2(X7,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                                  & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
                               => ( X7 = k10_tmap_1(X1,X2,X3,X4,X5,X6)
                                <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X7),X5)
                                    & r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X7),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_tmap_1)).

fof(t145_tmap_1,axiom,(
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
                 => ( r1_tsep_1(X3,X4)
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
                           => ( r4_tsep_1(X1,X3,X4)
                             => ( v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))
                                & v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                                & v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2)
                                & m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_tmap_1)).

fof(t85_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( ( r1_tsep_1(X2,X3)
                  & r4_tsep_1(X1,X2,X3) )
              <=> r3_tsep_1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tsep_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ( r3_tsep_1(X1,X2,X3)
                <=> ( r1_tsep_1(X2,X3)
                    & ! [X4] :
                        ( ( ~ v2_struct_0(X4)
                          & v2_pre_topc(X4)
                          & l1_pre_topc(X4) )
                       => ! [X5] :
                            ( ( v1_funct_1(X5)
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X4))
                              & v5_pre_topc(X5,X2,X4)
                              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4)))) )
                           => ! [X6] :
                                ( ( v1_funct_1(X6)
                                  & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X4))
                                  & v5_pre_topc(X6,X3,X4)
                                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))) )
                               => ( v1_funct_1(k10_tmap_1(X1,X4,X2,X3,X5,X6))
                                  & v1_funct_2(k10_tmap_1(X1,X4,X2,X3,X5,X6),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))
                                  & v5_pre_topc(k10_tmap_1(X1,X4,X2,X3,X5,X6),k1_tsep_1(X1,X2,X3),X4)
                                  & m1_subset_1(k10_tmap_1(X1,X4,X2,X3,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t150_tmap_1])).

fof(c_0_8,plain,(
    ! [X25,X26,X27,X28,X29] :
      ( ( r1_tsep_1(X26,X27)
        | ~ r3_tsep_1(X25,X26,X27)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( v1_funct_1(X29)
        | ~ v1_funct_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29))
        | ~ v1_funct_2(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),u1_struct_0(X26),u1_struct_0(X28))
        | ~ v5_pre_topc(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),X26,X28)
        | ~ m1_subset_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X28))))
        | ~ v1_funct_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29))
        | ~ v1_funct_2(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),u1_struct_0(X27),u1_struct_0(X28))
        | ~ v5_pre_topc(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),X27,X28)
        | ~ m1_subset_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28))))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(X28))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ r3_tsep_1(X25,X26,X27)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( v1_funct_2(X29,u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(X28))
        | ~ v1_funct_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29))
        | ~ v1_funct_2(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),u1_struct_0(X26),u1_struct_0(X28))
        | ~ v5_pre_topc(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),X26,X28)
        | ~ m1_subset_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X28))))
        | ~ v1_funct_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29))
        | ~ v1_funct_2(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),u1_struct_0(X27),u1_struct_0(X28))
        | ~ v5_pre_topc(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),X27,X28)
        | ~ m1_subset_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28))))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(X28))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ r3_tsep_1(X25,X26,X27)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( v5_pre_topc(X29,k1_tsep_1(X25,X26,X27),X28)
        | ~ v1_funct_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29))
        | ~ v1_funct_2(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),u1_struct_0(X26),u1_struct_0(X28))
        | ~ v5_pre_topc(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),X26,X28)
        | ~ m1_subset_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X28))))
        | ~ v1_funct_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29))
        | ~ v1_funct_2(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),u1_struct_0(X27),u1_struct_0(X28))
        | ~ v5_pre_topc(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),X27,X28)
        | ~ m1_subset_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28))))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(X28))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ r3_tsep_1(X25,X26,X27)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(X28))))
        | ~ v1_funct_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29))
        | ~ v1_funct_2(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),u1_struct_0(X26),u1_struct_0(X28))
        | ~ v5_pre_topc(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),X26,X28)
        | ~ m1_subset_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X28))))
        | ~ v1_funct_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29))
        | ~ v1_funct_2(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),u1_struct_0(X27),u1_struct_0(X28))
        | ~ v5_pre_topc(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),X27,X28)
        | ~ m1_subset_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28))))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(X28))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ r3_tsep_1(X25,X26,X27)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( ~ v2_struct_0(esk1_3(X25,X26,X27))
        | ~ r1_tsep_1(X26,X27)
        | r3_tsep_1(X25,X26,X27)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( v2_pre_topc(esk1_3(X25,X26,X27))
        | ~ r1_tsep_1(X26,X27)
        | r3_tsep_1(X25,X26,X27)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( l1_pre_topc(esk1_3(X25,X26,X27))
        | ~ r1_tsep_1(X26,X27)
        | r3_tsep_1(X25,X26,X27)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( v1_funct_1(esk2_3(X25,X26,X27))
        | ~ r1_tsep_1(X26,X27)
        | r3_tsep_1(X25,X26,X27)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( v1_funct_2(esk2_3(X25,X26,X27),u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(esk1_3(X25,X26,X27)))
        | ~ r1_tsep_1(X26,X27)
        | r3_tsep_1(X25,X26,X27)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( m1_subset_1(esk2_3(X25,X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(esk1_3(X25,X26,X27)))))
        | ~ r1_tsep_1(X26,X27)
        | r3_tsep_1(X25,X26,X27)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( v1_funct_1(k3_tmap_1(X25,esk1_3(X25,X26,X27),k1_tsep_1(X25,X26,X27),X26,esk2_3(X25,X26,X27)))
        | ~ r1_tsep_1(X26,X27)
        | r3_tsep_1(X25,X26,X27)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( v1_funct_2(k3_tmap_1(X25,esk1_3(X25,X26,X27),k1_tsep_1(X25,X26,X27),X26,esk2_3(X25,X26,X27)),u1_struct_0(X26),u1_struct_0(esk1_3(X25,X26,X27)))
        | ~ r1_tsep_1(X26,X27)
        | r3_tsep_1(X25,X26,X27)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( v5_pre_topc(k3_tmap_1(X25,esk1_3(X25,X26,X27),k1_tsep_1(X25,X26,X27),X26,esk2_3(X25,X26,X27)),X26,esk1_3(X25,X26,X27))
        | ~ r1_tsep_1(X26,X27)
        | r3_tsep_1(X25,X26,X27)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( m1_subset_1(k3_tmap_1(X25,esk1_3(X25,X26,X27),k1_tsep_1(X25,X26,X27),X26,esk2_3(X25,X26,X27)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(esk1_3(X25,X26,X27)))))
        | ~ r1_tsep_1(X26,X27)
        | r3_tsep_1(X25,X26,X27)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( v1_funct_1(k3_tmap_1(X25,esk1_3(X25,X26,X27),k1_tsep_1(X25,X26,X27),X27,esk2_3(X25,X26,X27)))
        | ~ r1_tsep_1(X26,X27)
        | r3_tsep_1(X25,X26,X27)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( v1_funct_2(k3_tmap_1(X25,esk1_3(X25,X26,X27),k1_tsep_1(X25,X26,X27),X27,esk2_3(X25,X26,X27)),u1_struct_0(X27),u1_struct_0(esk1_3(X25,X26,X27)))
        | ~ r1_tsep_1(X26,X27)
        | r3_tsep_1(X25,X26,X27)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( v5_pre_topc(k3_tmap_1(X25,esk1_3(X25,X26,X27),k1_tsep_1(X25,X26,X27),X27,esk2_3(X25,X26,X27)),X27,esk1_3(X25,X26,X27))
        | ~ r1_tsep_1(X26,X27)
        | r3_tsep_1(X25,X26,X27)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( m1_subset_1(k3_tmap_1(X25,esk1_3(X25,X26,X27),k1_tsep_1(X25,X26,X27),X27,esk2_3(X25,X26,X27)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(esk1_3(X25,X26,X27)))))
        | ~ r1_tsep_1(X26,X27)
        | r3_tsep_1(X25,X26,X27)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( ~ v1_funct_1(esk2_3(X25,X26,X27))
        | ~ v1_funct_2(esk2_3(X25,X26,X27),u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(esk1_3(X25,X26,X27)))
        | ~ v5_pre_topc(esk2_3(X25,X26,X27),k1_tsep_1(X25,X26,X27),esk1_3(X25,X26,X27))
        | ~ m1_subset_1(esk2_3(X25,X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(esk1_3(X25,X26,X27)))))
        | ~ r1_tsep_1(X26,X27)
        | r3_tsep_1(X25,X26,X27)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t135_tmap_1])])])])])])).

fof(c_0_9,negated_conjecture,(
    ! [X47,X48,X49] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk3_0)
      & ~ v2_struct_0(esk5_0)
      & m1_pre_topc(esk5_0,esk3_0)
      & ( ~ v2_struct_0(esk6_0)
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v2_pre_topc(esk6_0)
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( l1_pre_topc(esk6_0)
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v1_funct_1(esk7_0)
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk6_0))
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v5_pre_topc(esk7_0,esk4_0,esk6_0)
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk6_0))))
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v1_funct_1(esk8_0)
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk6_0))
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v5_pre_topc(esk8_0,esk5_0,esk6_0)
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( ~ v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0))
        | ~ v1_funct_2(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))
        | ~ v5_pre_topc(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk6_0)
        | ~ m1_subset_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))))
        | ~ r1_tsep_1(esk4_0,esk5_0)
        | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( r1_tsep_1(esk4_0,esk5_0)
        | r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v1_funct_1(k10_tmap_1(esk3_0,X47,esk4_0,esk5_0,X48,X49))
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(esk5_0),u1_struct_0(X47))
        | ~ v5_pre_topc(X49,esk5_0,X47)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X47))))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(esk4_0),u1_struct_0(X47))
        | ~ v5_pre_topc(X48,esk4_0,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X47))))
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47)
        | r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v1_funct_2(k10_tmap_1(esk3_0,X47,esk4_0,esk5_0,X48,X49),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X47))
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(esk5_0),u1_struct_0(X47))
        | ~ v5_pre_topc(X49,esk5_0,X47)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X47))))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(esk4_0),u1_struct_0(X47))
        | ~ v5_pre_topc(X48,esk4_0,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X47))))
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47)
        | r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( v5_pre_topc(k10_tmap_1(esk3_0,X47,esk4_0,esk5_0,X48,X49),k1_tsep_1(esk3_0,esk4_0,esk5_0),X47)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(esk5_0),u1_struct_0(X47))
        | ~ v5_pre_topc(X49,esk5_0,X47)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X47))))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(esk4_0),u1_struct_0(X47))
        | ~ v5_pre_topc(X48,esk4_0,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X47))))
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47)
        | r3_tsep_1(esk3_0,esk4_0,esk5_0) )
      & ( m1_subset_1(k10_tmap_1(esk3_0,X47,esk4_0,esk5_0,X48,X49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X47))))
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(esk5_0),u1_struct_0(X47))
        | ~ v5_pre_topc(X49,esk5_0,X47)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X47))))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(esk4_0),u1_struct_0(X47))
        | ~ v5_pre_topc(X48,esk4_0,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X47))))
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47)
        | r3_tsep_1(esk3_0,esk4_0,esk5_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])])).

cnf(c_0_10,plain,
    ( r1_tsep_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r3_tsep_1(X3,X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk5_0)
    | r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( ~ v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0))
    | ~ v1_funct_2(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))
    | ~ v5_pre_topc(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk6_0)
    | ~ m1_subset_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( r1_tsep_1(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_17]),c_0_18])).

fof(c_0_21,plain,(
    ! [X19,X20,X21,X22,X23,X24] :
      ( ( v1_funct_1(k10_tmap_1(X19,X20,X21,X22,X23,X24))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X19)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X19)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X20))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20))))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X20))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X20)))) )
      & ( v1_funct_2(k10_tmap_1(X19,X20,X21,X22,X23,X24),u1_struct_0(k1_tsep_1(X19,X21,X22)),u1_struct_0(X20))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X19)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X19)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X20))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20))))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X20))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X20)))) )
      & ( m1_subset_1(k10_tmap_1(X19,X20,X21,X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X19,X21,X22)),u1_struct_0(X20))))
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X19)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X19)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X20))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20))))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X20))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X20)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_tmap_1])])])])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk7_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk8_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk6_0))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk6_0))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk6_0))))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,negated_conjecture,
    ( v2_pre_topc(esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_31,plain,(
    ! [X8,X9,X10,X11] :
      ( ( ~ r2_funct_2(X8,X9,X10,X11)
        | X10 = X11
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X8,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
      & ( X10 != X11
        | r2_funct_2(X8,X9,X10,X11)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X8,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_32,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk6_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ m1_subset_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))))
    | ~ v1_funct_2(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))
    | ~ v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20])])).

cnf(c_0_33,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk7_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_20])])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk8_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_20])])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk6_0))
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_20])])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk6_0))
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_20])])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk6_0))))
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_20])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_20])])).

cnf(c_0_40,negated_conjecture,
    ( v2_pre_topc(esk6_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_20])])).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk6_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_20])])).

cnf(c_0_42,negated_conjecture,
    ( ~ r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ v2_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_20])])).

fof(c_0_43,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_funct_2(u1_struct_0(X14),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X14,X18),X16)
        | X18 != k10_tmap_1(X12,X13,X14,X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))))
        | ~ r1_tsep_1(X14,X15)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13))))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13))))
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_funct_2(u1_struct_0(X15),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X15,X18),X17)
        | X18 != k10_tmap_1(X12,X13,X14,X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))))
        | ~ r1_tsep_1(X14,X15)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13))))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13))))
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_funct_2(u1_struct_0(X14),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X14,X18),X16)
        | ~ r2_funct_2(u1_struct_0(X15),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X15,X18),X17)
        | X18 = k10_tmap_1(X12,X13,X14,X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))))
        | ~ r1_tsep_1(X14,X15)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13))))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13))))
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_funct_2(u1_struct_0(X14),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X14,X18),X16)
        | X18 != k10_tmap_1(X12,X13,X14,X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))))
        | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X12,X14,X15)),u1_struct_0(X13),k3_tmap_1(X12,X13,X14,k2_tsep_1(X12,X14,X15),X16),k3_tmap_1(X12,X13,X15,k2_tsep_1(X12,X14,X15),X17))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13))))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13))))
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_funct_2(u1_struct_0(X15),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X15,X18),X17)
        | X18 != k10_tmap_1(X12,X13,X14,X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))))
        | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X12,X14,X15)),u1_struct_0(X13),k3_tmap_1(X12,X13,X14,k2_tsep_1(X12,X14,X15),X16),k3_tmap_1(X12,X13,X15,k2_tsep_1(X12,X14,X15),X17))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13))))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13))))
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_funct_2(u1_struct_0(X14),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X14,X18),X16)
        | ~ r2_funct_2(u1_struct_0(X15),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X15,X18),X17)
        | X18 = k10_tmap_1(X12,X13,X14,X15,X16,X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))))
        | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X12,X14,X15)),u1_struct_0(X13),k3_tmap_1(X12,X13,X14,k2_tsep_1(X12,X14,X15),X16),k3_tmap_1(X12,X13,X15,k2_tsep_1(X12,X14,X15),X17))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13))))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13))))
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X12)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X12)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_tmap_1])])])])])).

cnf(c_0_44,plain,
    ( r2_funct_2(X3,X4,X1,X2)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk6_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ v1_funct_2(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))
    | ~ v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_17]),c_0_18]),c_0_16]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_46,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_47,plain,(
    ! [X32,X33,X34,X35,X36,X37] :
      ( ( v1_funct_1(k10_tmap_1(X32,X33,X34,X35,X36,X37))
        | ~ r4_tsep_1(X32,X34,X35)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,u1_struct_0(X35),u1_struct_0(X33))
        | ~ v5_pre_topc(X37,X35,X33)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X33))))
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X33))
        | ~ v5_pre_topc(X36,X34,X33)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X33))))
        | ~ r1_tsep_1(X34,X35)
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X32)
        | v2_struct_0(X34)
        | ~ m1_pre_topc(X34,X32)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( v1_funct_2(k10_tmap_1(X32,X33,X34,X35,X36,X37),u1_struct_0(k1_tsep_1(X32,X34,X35)),u1_struct_0(X33))
        | ~ r4_tsep_1(X32,X34,X35)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,u1_struct_0(X35),u1_struct_0(X33))
        | ~ v5_pre_topc(X37,X35,X33)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X33))))
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X33))
        | ~ v5_pre_topc(X36,X34,X33)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X33))))
        | ~ r1_tsep_1(X34,X35)
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X32)
        | v2_struct_0(X34)
        | ~ m1_pre_topc(X34,X32)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( v5_pre_topc(k10_tmap_1(X32,X33,X34,X35,X36,X37),k1_tsep_1(X32,X34,X35),X33)
        | ~ r4_tsep_1(X32,X34,X35)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,u1_struct_0(X35),u1_struct_0(X33))
        | ~ v5_pre_topc(X37,X35,X33)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X33))))
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X33))
        | ~ v5_pre_topc(X36,X34,X33)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X33))))
        | ~ r1_tsep_1(X34,X35)
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X32)
        | v2_struct_0(X34)
        | ~ m1_pre_topc(X34,X32)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( m1_subset_1(k10_tmap_1(X32,X33,X34,X35,X36,X37),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X32,X34,X35)),u1_struct_0(X33))))
        | ~ r4_tsep_1(X32,X34,X35)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,u1_struct_0(X35),u1_struct_0(X33))
        | ~ v5_pre_topc(X37,X35,X33)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X33))))
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X33))
        | ~ v5_pre_topc(X36,X34,X33)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X33))))
        | ~ r1_tsep_1(X34,X35)
        | v2_struct_0(X35)
        | ~ m1_pre_topc(X35,X32)
        | v2_struct_0(X34)
        | ~ m1_pre_topc(X34,X32)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33)
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t145_tmap_1])])])])])).

cnf(c_0_48,negated_conjecture,
    ( v5_pre_topc(esk7_0,esk4_0,esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_49,negated_conjecture,
    ( v5_pre_topc(esk8_0,esk5_0,esk6_0)
    | ~ r1_tsep_1(esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_50,plain,
    ( X5 = k10_tmap_1(X3,X2,X1,X4,X6,X7)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X1,X5),X6)
    | ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X4,X5),X7)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))))
    | ~ r1_tsep_1(X1,X4)
    | ~ v1_funct_1(X7)
    | ~ v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk6_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_17]),c_0_18]),c_0_16]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_53,plain,
    ( v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r4_tsep_1(X1,X3,X4)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
    | ~ v5_pre_topc(X6,X4,X2)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ r1_tsep_1(X3,X4)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( v5_pre_topc(esk7_0,esk4_0,esk6_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_20])])).

cnf(c_0_55,negated_conjecture,
    ( v5_pre_topc(esk8_0,esk5_0,esk6_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_20])])).

cnf(c_0_56,plain,
    ( k10_tmap_1(X1,X2,X3,X4,X5,k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X6)) = X6
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ r1_tsep_1(X3,X4)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X6),X5)
    | ~ m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X6),u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X6))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X6) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,plain,
    ( m1_subset_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(esk1_3(X1,X2,X3)))))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_58,plain,
    ( v1_funct_1(esk2_3(X1,X2,X3))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_59,plain,
    ( v1_funct_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_60,plain,
    ( v1_funct_2(esk2_3(X1,X2,X3),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_61,plain,
    ( v1_funct_2(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)),u1_struct_0(X3),u1_struct_0(esk1_3(X1,X2,X3)))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_62,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_63,plain,
    ( v2_pre_topc(esk1_3(X1,X2,X3))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_64,plain,
    ( l1_pre_topc(esk1_3(X1,X2,X3))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_65,plain,
    ( r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk1_3(X1,X2,X3))
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_66,negated_conjecture,
    ( ~ r4_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_20]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_17]),c_0_18]),c_0_16]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_54]),c_0_55]),c_0_42])).

cnf(c_0_67,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_68,plain,(
    ! [X38,X39,X40] :
      ( ( ~ r1_tsep_1(X39,X40)
        | ~ r4_tsep_1(X38,X39,X40)
        | r3_tsep_1(X38,X39,X40)
        | v2_struct_0(X40)
        | ~ m1_pre_topc(X40,X38)
        | v2_struct_0(X39)
        | ~ m1_pre_topc(X39,X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( r1_tsep_1(X39,X40)
        | ~ r3_tsep_1(X38,X39,X40)
        | v2_struct_0(X40)
        | ~ m1_pre_topc(X40,X38)
        | v2_struct_0(X39)
        | ~ m1_pre_topc(X39,X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( r4_tsep_1(X38,X39,X40)
        | ~ r3_tsep_1(X38,X39,X40)
        | v2_struct_0(X40)
        | ~ m1_pre_topc(X40,X38)
        | v2_struct_0(X39)
        | ~ m1_pre_topc(X39,X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t85_tsep_1])])])])])).

cnf(c_0_69,plain,
    ( k10_tmap_1(X1,esk1_3(X1,X2,X3),X2,X3,X4,k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3))) = esk2_3(X1,X2,X3)
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(esk1_3(X1,X2,X3)),k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk1_3(X1,X2,X3)))))
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(esk1_3(X1,X2,X3)))
    | ~ v1_funct_1(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_59]),c_0_60]),c_0_61]),c_0_62]),c_0_63]),c_0_64]),c_0_65])).

cnf(c_0_70,plain,
    ( v1_funct_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_71,plain,
    ( v1_funct_2(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)),u1_struct_0(X2),u1_struct_0(esk1_3(X1,X2,X3)))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_72,plain,
    ( m1_subset_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk1_3(X1,X2,X3)))))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_73,negated_conjecture,
    ( ~ r4_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_17]),c_0_18]),c_0_16]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_74,plain,
    ( r4_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_tsep_1(X1,X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( v5_pre_topc(k10_tmap_1(esk3_0,X1,esk4_0,esk5_0,X2,X3),k1_tsep_1(esk3_0,esk4_0,esk5_0),X1)
    | v2_struct_0(X1)
    | r3_tsep_1(esk3_0,esk4_0,esk5_0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(esk5_0),u1_struct_0(X1))
    | ~ v5_pre_topc(X3,esk5_0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))
    | ~ v5_pre_topc(X2,esk4_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_76,plain,
    ( k10_tmap_1(X1,esk1_3(X1,X2,X3),X2,X3,k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)),k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3))) = esk2_3(X1,X2,X3)
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_51]),c_0_70]),c_0_71]),c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( ~ r3_tsep_1(esk3_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_17]),c_0_18]),c_0_16])).

cnf(c_0_78,negated_conjecture,
    ( v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ m1_subset_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_20]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_77]),c_0_18]),c_0_16]),c_0_17])).

cnf(c_0_79,negated_conjecture,
    ( v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_57]),c_0_20]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_77]),c_0_17]),c_0_18]),c_0_16])).

cnf(c_0_80,negated_conjecture,
    ( v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_72]),c_0_20]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_77]),c_0_17]),c_0_18]),c_0_16])).

cnf(c_0_81,negated_conjecture,
    ( v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_61]),c_0_20]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_77]),c_0_17]),c_0_18]),c_0_16])).

cnf(c_0_82,negated_conjecture,
    ( v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_71]),c_0_20]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_77]),c_0_17]),c_0_18]),c_0_16])).

cnf(c_0_83,plain,
    ( v5_pre_topc(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)),X3,esk1_3(X1,X2,X3))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_84,negated_conjecture,
    ( v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_20]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_77]),c_0_17]),c_0_18]),c_0_16])).

cnf(c_0_85,plain,
    ( v5_pre_topc(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)),X2,esk1_3(X1,X2,X3))
    | r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_86,negated_conjecture,
    ( v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_20]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_77]),c_0_17]),c_0_18]),c_0_16])).

cnf(c_0_87,plain,
    ( r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(esk2_3(X1,X2,X3))
    | ~ v1_funct_2(esk2_3(X1,X2,X3),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))
    | ~ v5_pre_topc(esk2_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),esk1_3(X1,X2,X3))
    | ~ m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))))
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_88,negated_conjecture,
    ( v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_59]),c_0_20]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_77]),c_0_17]),c_0_18]),c_0_16])).

cnf(c_0_89,plain,
    ( r3_tsep_1(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v5_pre_topc(esk2_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),esk1_3(X1,X2,X3))
    | ~ r1_tsep_1(X2,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_87,c_0_58]),c_0_60]),c_0_62])).

cnf(c_0_90,negated_conjecture,
    ( v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_70]),c_0_20]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_77]),c_0_17]),c_0_18]),c_0_16])).

cnf(c_0_91,negated_conjecture,
    ( v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_20]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_77]),c_0_17]),c_0_18]),c_0_16])).

cnf(c_0_92,negated_conjecture,
    ( v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_64]),c_0_20]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_77]),c_0_17]),c_0_18]),c_0_16])).

cnf(c_0_93,negated_conjecture,
    ( v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_63]),c_0_20]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_77]),c_0_17]),c_0_18]),c_0_16])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_93]),c_0_20]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_77]),c_0_17]),c_0_18]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:07:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.62/0.79  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039N
% 0.62/0.79  # and selection function PSelectUnlessUniqMaxPos.
% 0.62/0.79  #
% 0.62/0.79  # Preprocessing time       : 0.033 s
% 0.62/0.79  # Presaturation interreduction done
% 0.62/0.79  
% 0.62/0.79  # Proof found!
% 0.62/0.79  # SZS status Theorem
% 0.62/0.79  # SZS output start CNFRefutation
% 0.62/0.79  fof(t150_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(r3_tsep_1(X1,X2,X3)<=>(r1_tsep_1(X2,X3)&![X4]:(((~(v2_struct_0(X4))&v2_pre_topc(X4))&l1_pre_topc(X4))=>![X5]:((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X4)))&v5_pre_topc(X5,X2,X4))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4)))))=>![X6]:((((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X4)))&v5_pre_topc(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))))=>(((v1_funct_1(k10_tmap_1(X1,X4,X2,X3,X5,X6))&v1_funct_2(k10_tmap_1(X1,X4,X2,X3,X5,X6),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))&v5_pre_topc(k10_tmap_1(X1,X4,X2,X3,X5,X6),k1_tsep_1(X1,X2,X3),X4))&m1_subset_1(k10_tmap_1(X1,X4,X2,X3,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_tmap_1)).
% 0.62/0.79  fof(t135_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(r3_tsep_1(X1,X2,X3)<=>(r1_tsep_1(X2,X3)&![X4]:(((~(v2_struct_0(X4))&v2_pre_topc(X4))&l1_pre_topc(X4))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))))=>((((((((v1_funct_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5))&v1_funct_2(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5),u1_struct_0(X2),u1_struct_0(X4)))&v5_pre_topc(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5),X2,X4))&m1_subset_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4)))))&v1_funct_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5)))&v1_funct_2(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5),u1_struct_0(X3),u1_struct_0(X4)))&v5_pre_topc(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5),X3,X4))&m1_subset_1(k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))))=>(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))&v5_pre_topc(X5,k1_tsep_1(X1,X2,X3),X4))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_tmap_1)).
% 0.62/0.79  fof(dt_k10_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))&~(v2_struct_0(X4)))&m1_pre_topc(X4,X1))&v1_funct_1(X5))&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(X6))&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 0.62/0.79  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.62/0.79  fof(d13_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((r1_tsep_1(X3,X4)|r2_funct_2(u1_struct_0(k2_tsep_1(X1,X3,X4)),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,k2_tsep_1(X1,X3,X4),X5),k3_tmap_1(X1,X2,X4,k2_tsep_1(X1,X3,X4),X6)))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))=>(X7=k10_tmap_1(X1,X2,X3,X4,X5,X6)<=>(r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X7),X5)&r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X7),X6))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_tmap_1)).
% 0.62/0.79  fof(t145_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(r1_tsep_1(X3,X4)=>![X5]:((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X6]:((((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(r4_tsep_1(X1,X3,X4)=>(((v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_tmap_1)).
% 0.62/0.79  fof(t85_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>((r1_tsep_1(X2,X3)&r4_tsep_1(X1,X2,X3))<=>r3_tsep_1(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_tsep_1)).
% 0.62/0.79  fof(c_0_7, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(r3_tsep_1(X1,X2,X3)<=>(r1_tsep_1(X2,X3)&![X4]:(((~(v2_struct_0(X4))&v2_pre_topc(X4))&l1_pre_topc(X4))=>![X5]:((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X4)))&v5_pre_topc(X5,X2,X4))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4)))))=>![X6]:((((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X4)))&v5_pre_topc(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))))=>(((v1_funct_1(k10_tmap_1(X1,X4,X2,X3,X5,X6))&v1_funct_2(k10_tmap_1(X1,X4,X2,X3,X5,X6),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))&v5_pre_topc(k10_tmap_1(X1,X4,X2,X3,X5,X6),k1_tsep_1(X1,X2,X3),X4))&m1_subset_1(k10_tmap_1(X1,X4,X2,X3,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4)))))))))))))), inference(assume_negation,[status(cth)],[t150_tmap_1])).
% 0.62/0.79  fof(c_0_8, plain, ![X25, X26, X27, X28, X29]:(((r1_tsep_1(X26,X27)|~r3_tsep_1(X25,X26,X27)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))&((((v1_funct_1(X29)|(~v1_funct_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29))|~v1_funct_2(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),u1_struct_0(X26),u1_struct_0(X28))|~v5_pre_topc(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),X26,X28)|~m1_subset_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X28))))|~v1_funct_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29))|~v1_funct_2(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),u1_struct_0(X27),u1_struct_0(X28))|~v5_pre_topc(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),X27,X28)|~m1_subset_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28)))))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(X28)))))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))|~r3_tsep_1(X25,X26,X27)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))&(v1_funct_2(X29,u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(X28))|(~v1_funct_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29))|~v1_funct_2(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),u1_struct_0(X26),u1_struct_0(X28))|~v5_pre_topc(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),X26,X28)|~m1_subset_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X28))))|~v1_funct_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29))|~v1_funct_2(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),u1_struct_0(X27),u1_struct_0(X28))|~v5_pre_topc(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),X27,X28)|~m1_subset_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28)))))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(X28)))))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))|~r3_tsep_1(X25,X26,X27)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25))))&(v5_pre_topc(X29,k1_tsep_1(X25,X26,X27),X28)|(~v1_funct_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29))|~v1_funct_2(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),u1_struct_0(X26),u1_struct_0(X28))|~v5_pre_topc(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),X26,X28)|~m1_subset_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X28))))|~v1_funct_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29))|~v1_funct_2(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),u1_struct_0(X27),u1_struct_0(X28))|~v5_pre_topc(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),X27,X28)|~m1_subset_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28)))))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(X28)))))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))|~r3_tsep_1(X25,X26,X27)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25))))&(m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(X28))))|(~v1_funct_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29))|~v1_funct_2(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),u1_struct_0(X26),u1_struct_0(X28))|~v5_pre_topc(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),X26,X28)|~m1_subset_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X26,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X28))))|~v1_funct_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29))|~v1_funct_2(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),u1_struct_0(X27),u1_struct_0(X28))|~v5_pre_topc(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),X27,X28)|~m1_subset_1(k3_tmap_1(X25,X28,k1_tsep_1(X25,X26,X27),X27,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28)))))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(X28)))))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))|~r3_tsep_1(X25,X26,X27)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))))&((((~v2_struct_0(esk1_3(X25,X26,X27))|~r1_tsep_1(X26,X27)|r3_tsep_1(X25,X26,X27)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))&(v2_pre_topc(esk1_3(X25,X26,X27))|~r1_tsep_1(X26,X27)|r3_tsep_1(X25,X26,X27)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25))))&(l1_pre_topc(esk1_3(X25,X26,X27))|~r1_tsep_1(X26,X27)|r3_tsep_1(X25,X26,X27)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25))))&((((v1_funct_1(esk2_3(X25,X26,X27))|~r1_tsep_1(X26,X27)|r3_tsep_1(X25,X26,X27)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))&(v1_funct_2(esk2_3(X25,X26,X27),u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(esk1_3(X25,X26,X27)))|~r1_tsep_1(X26,X27)|r3_tsep_1(X25,X26,X27)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25))))&(m1_subset_1(esk2_3(X25,X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(esk1_3(X25,X26,X27)))))|~r1_tsep_1(X26,X27)|r3_tsep_1(X25,X26,X27)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25))))&(((((((((v1_funct_1(k3_tmap_1(X25,esk1_3(X25,X26,X27),k1_tsep_1(X25,X26,X27),X26,esk2_3(X25,X26,X27)))|~r1_tsep_1(X26,X27)|r3_tsep_1(X25,X26,X27)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))&(v1_funct_2(k3_tmap_1(X25,esk1_3(X25,X26,X27),k1_tsep_1(X25,X26,X27),X26,esk2_3(X25,X26,X27)),u1_struct_0(X26),u1_struct_0(esk1_3(X25,X26,X27)))|~r1_tsep_1(X26,X27)|r3_tsep_1(X25,X26,X27)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25))))&(v5_pre_topc(k3_tmap_1(X25,esk1_3(X25,X26,X27),k1_tsep_1(X25,X26,X27),X26,esk2_3(X25,X26,X27)),X26,esk1_3(X25,X26,X27))|~r1_tsep_1(X26,X27)|r3_tsep_1(X25,X26,X27)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25))))&(m1_subset_1(k3_tmap_1(X25,esk1_3(X25,X26,X27),k1_tsep_1(X25,X26,X27),X26,esk2_3(X25,X26,X27)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(esk1_3(X25,X26,X27)))))|~r1_tsep_1(X26,X27)|r3_tsep_1(X25,X26,X27)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25))))&(v1_funct_1(k3_tmap_1(X25,esk1_3(X25,X26,X27),k1_tsep_1(X25,X26,X27),X27,esk2_3(X25,X26,X27)))|~r1_tsep_1(X26,X27)|r3_tsep_1(X25,X26,X27)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25))))&(v1_funct_2(k3_tmap_1(X25,esk1_3(X25,X26,X27),k1_tsep_1(X25,X26,X27),X27,esk2_3(X25,X26,X27)),u1_struct_0(X27),u1_struct_0(esk1_3(X25,X26,X27)))|~r1_tsep_1(X26,X27)|r3_tsep_1(X25,X26,X27)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25))))&(v5_pre_topc(k3_tmap_1(X25,esk1_3(X25,X26,X27),k1_tsep_1(X25,X26,X27),X27,esk2_3(X25,X26,X27)),X27,esk1_3(X25,X26,X27))|~r1_tsep_1(X26,X27)|r3_tsep_1(X25,X26,X27)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25))))&(m1_subset_1(k3_tmap_1(X25,esk1_3(X25,X26,X27),k1_tsep_1(X25,X26,X27),X27,esk2_3(X25,X26,X27)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(esk1_3(X25,X26,X27)))))|~r1_tsep_1(X26,X27)|r3_tsep_1(X25,X26,X27)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25))))&(~v1_funct_1(esk2_3(X25,X26,X27))|~v1_funct_2(esk2_3(X25,X26,X27),u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(esk1_3(X25,X26,X27)))|~v5_pre_topc(esk2_3(X25,X26,X27),k1_tsep_1(X25,X26,X27),esk1_3(X25,X26,X27))|~m1_subset_1(esk2_3(X25,X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X25,X26,X27)),u1_struct_0(esk1_3(X25,X26,X27)))))|~r1_tsep_1(X26,X27)|r3_tsep_1(X25,X26,X27)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t135_tmap_1])])])])])])).
% 0.62/0.79  fof(c_0_9, negated_conjecture, ![X47, X48, X49]:(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk3_0))&(((((~v2_struct_0(esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0))&(v2_pre_topc(esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(l1_pre_topc(esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(((((v1_funct_1(esk7_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0))&(v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk6_0))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(v5_pre_topc(esk7_0,esk4_0,esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk6_0))))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(((((v1_funct_1(esk8_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0))&(v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk6_0))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(v5_pre_topc(esk8_0,esk5_0,esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(~v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0))|~v1_funct_2(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))|~v5_pre_topc(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk6_0)|~m1_subset_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)))))&((r1_tsep_1(esk4_0,esk5_0)|r3_tsep_1(esk3_0,esk4_0,esk5_0))&((((v1_funct_1(k10_tmap_1(esk3_0,X47,esk4_0,esk5_0,X48,X49))|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(esk5_0),u1_struct_0(X47))|~v5_pre_topc(X49,esk5_0,X47)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X47)))))|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(esk4_0),u1_struct_0(X47))|~v5_pre_topc(X48,esk4_0,X47)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X47)))))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47))|r3_tsep_1(esk3_0,esk4_0,esk5_0))&(v1_funct_2(k10_tmap_1(esk3_0,X47,esk4_0,esk5_0,X48,X49),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X47))|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(esk5_0),u1_struct_0(X47))|~v5_pre_topc(X49,esk5_0,X47)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X47)))))|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(esk4_0),u1_struct_0(X47))|~v5_pre_topc(X48,esk4_0,X47)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X47)))))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47))|r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(v5_pre_topc(k10_tmap_1(esk3_0,X47,esk4_0,esk5_0,X48,X49),k1_tsep_1(esk3_0,esk4_0,esk5_0),X47)|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(esk5_0),u1_struct_0(X47))|~v5_pre_topc(X49,esk5_0,X47)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X47)))))|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(esk4_0),u1_struct_0(X47))|~v5_pre_topc(X48,esk4_0,X47)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X47)))))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47))|r3_tsep_1(esk3_0,esk4_0,esk5_0)))&(m1_subset_1(k10_tmap_1(esk3_0,X47,esk4_0,esk5_0,X48,X49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(X47))))|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(esk5_0),u1_struct_0(X47))|~v5_pre_topc(X49,esk5_0,X47)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X47)))))|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(esk4_0),u1_struct_0(X47))|~v5_pre_topc(X48,esk4_0,X47)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X47)))))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47))|r3_tsep_1(esk3_0,esk4_0,esk5_0)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])])).
% 0.62/0.79  cnf(c_0_10, plain, (r1_tsep_1(X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X3)|~r3_tsep_1(X3,X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.62/0.79  cnf(c_0_11, negated_conjecture, (r1_tsep_1(esk4_0,esk5_0)|r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.62/0.79  cnf(c_0_12, negated_conjecture, (m1_pre_topc(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.62/0.79  cnf(c_0_13, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.62/0.79  cnf(c_0_14, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.62/0.79  cnf(c_0_15, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.62/0.79  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.62/0.79  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.62/0.79  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.62/0.79  cnf(c_0_19, negated_conjecture, (~v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0))|~v1_funct_2(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))|~v5_pre_topc(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk6_0)|~m1_subset_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.62/0.79  cnf(c_0_20, negated_conjecture, (r1_tsep_1(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_16]), c_0_17]), c_0_18])).
% 0.62/0.79  fof(c_0_21, plain, ![X19, X20, X21, X22, X23, X24]:(((v1_funct_1(k10_tmap_1(X19,X20,X21,X22,X23,X24))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)|v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|v2_struct_0(X21)|~m1_pre_topc(X21,X19)|v2_struct_0(X22)|~m1_pre_topc(X22,X19)|~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X20))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20))))|~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X20))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X20))))))&(v1_funct_2(k10_tmap_1(X19,X20,X21,X22,X23,X24),u1_struct_0(k1_tsep_1(X19,X21,X22)),u1_struct_0(X20))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)|v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|v2_struct_0(X21)|~m1_pre_topc(X21,X19)|v2_struct_0(X22)|~m1_pre_topc(X22,X19)|~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X20))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20))))|~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X20))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X20)))))))&(m1_subset_1(k10_tmap_1(X19,X20,X21,X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X19,X21,X22)),u1_struct_0(X20))))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)|v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|v2_struct_0(X21)|~m1_pre_topc(X21,X19)|v2_struct_0(X22)|~m1_pre_topc(X22,X19)|~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X20))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X20))))|~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X20))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X20))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_tmap_1])])])])).
% 0.62/0.79  cnf(c_0_22, negated_conjecture, (v1_funct_1(esk7_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.62/0.79  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk8_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.62/0.79  cnf(c_0_24, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk6_0))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.62/0.79  cnf(c_0_25, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk6_0))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.62/0.79  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk6_0))))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.62/0.79  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.62/0.79  cnf(c_0_28, negated_conjecture, (v2_pre_topc(esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.62/0.79  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.62/0.79  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.62/0.79  fof(c_0_31, plain, ![X8, X9, X10, X11]:((~r2_funct_2(X8,X9,X10,X11)|X10=X11|(~v1_funct_1(X10)|~v1_funct_2(X10,X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))|~v1_funct_1(X11)|~v1_funct_2(X11,X8,X9)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))))&(X10!=X11|r2_funct_2(X8,X9,X10,X11)|(~v1_funct_1(X10)|~v1_funct_2(X10,X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))|~v1_funct_1(X11)|~v1_funct_2(X11,X8,X9)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.62/0.79  cnf(c_0_32, negated_conjecture, (~v5_pre_topc(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk6_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)|~m1_subset_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))))|~v1_funct_2(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))|~v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20])])).
% 0.62/0.79  cnf(c_0_33, plain, (m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.62/0.79  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk7_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_20])])).
% 0.62/0.79  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk8_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_20])])).
% 0.62/0.79  cnf(c_0_36, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk6_0))|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_20])])).
% 0.62/0.79  cnf(c_0_37, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk6_0))|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_20])])).
% 0.62/0.79  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk6_0))))|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_20])])).
% 0.62/0.79  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0))))|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_20])])).
% 0.62/0.79  cnf(c_0_40, negated_conjecture, (v2_pre_topc(esk6_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_20])])).
% 0.62/0.79  cnf(c_0_41, negated_conjecture, (l1_pre_topc(esk6_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_20])])).
% 0.62/0.79  cnf(c_0_42, negated_conjecture, (~r3_tsep_1(esk3_0,esk4_0,esk5_0)|~v2_struct_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_20])])).
% 0.62/0.79  fof(c_0_43, plain, ![X12, X13, X14, X15, X16, X17, X18]:((((r2_funct_2(u1_struct_0(X14),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X14,X18),X16)|X18!=k10_tmap_1(X12,X13,X14,X15,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13)))))|~r1_tsep_1(X14,X15)|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13)))))|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13)))))|(v2_struct_0(X15)|~m1_pre_topc(X15,X12))|(v2_struct_0(X14)|~m1_pre_topc(X14,X12))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(r2_funct_2(u1_struct_0(X15),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X15,X18),X17)|X18!=k10_tmap_1(X12,X13,X14,X15,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13)))))|~r1_tsep_1(X14,X15)|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13)))))|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13)))))|(v2_struct_0(X15)|~m1_pre_topc(X15,X12))|(v2_struct_0(X14)|~m1_pre_topc(X14,X12))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12))))&(~r2_funct_2(u1_struct_0(X14),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X14,X18),X16)|~r2_funct_2(u1_struct_0(X15),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X15,X18),X17)|X18=k10_tmap_1(X12,X13,X14,X15,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13)))))|~r1_tsep_1(X14,X15)|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13)))))|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13)))))|(v2_struct_0(X15)|~m1_pre_topc(X15,X12))|(v2_struct_0(X14)|~m1_pre_topc(X14,X12))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12))))&(((r2_funct_2(u1_struct_0(X14),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X14,X18),X16)|X18!=k10_tmap_1(X12,X13,X14,X15,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13)))))|~r2_funct_2(u1_struct_0(k2_tsep_1(X12,X14,X15)),u1_struct_0(X13),k3_tmap_1(X12,X13,X14,k2_tsep_1(X12,X14,X15),X16),k3_tmap_1(X12,X13,X15,k2_tsep_1(X12,X14,X15),X17))|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13)))))|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13)))))|(v2_struct_0(X15)|~m1_pre_topc(X15,X12))|(v2_struct_0(X14)|~m1_pre_topc(X14,X12))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(r2_funct_2(u1_struct_0(X15),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X15,X18),X17)|X18!=k10_tmap_1(X12,X13,X14,X15,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13)))))|~r2_funct_2(u1_struct_0(k2_tsep_1(X12,X14,X15)),u1_struct_0(X13),k3_tmap_1(X12,X13,X14,k2_tsep_1(X12,X14,X15),X16),k3_tmap_1(X12,X13,X15,k2_tsep_1(X12,X14,X15),X17))|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13)))))|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13)))))|(v2_struct_0(X15)|~m1_pre_topc(X15,X12))|(v2_struct_0(X14)|~m1_pre_topc(X14,X12))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12))))&(~r2_funct_2(u1_struct_0(X14),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X14,X18),X16)|~r2_funct_2(u1_struct_0(X15),u1_struct_0(X13),k3_tmap_1(X12,X13,k1_tsep_1(X12,X14,X15),X15,X18),X17)|X18=k10_tmap_1(X12,X13,X14,X15,X16,X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X12,X14,X15)),u1_struct_0(X13)))))|~r2_funct_2(u1_struct_0(k2_tsep_1(X12,X14,X15)),u1_struct_0(X13),k3_tmap_1(X12,X13,X14,k2_tsep_1(X12,X14,X15),X16),k3_tmap_1(X12,X13,X15,k2_tsep_1(X12,X14,X15),X17))|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X13))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X13)))))|(~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X13))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X13)))))|(v2_struct_0(X15)|~m1_pre_topc(X15,X12))|(v2_struct_0(X14)|~m1_pre_topc(X14,X12))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_tmap_1])])])])])).
% 0.62/0.79  cnf(c_0_44, plain, (r2_funct_2(X3,X4,X1,X2)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.62/0.79  cnf(c_0_45, negated_conjecture, (~v5_pre_topc(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk6_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)|~v1_funct_2(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk6_0))|~v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_17]), c_0_18]), c_0_16]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.62/0.79  cnf(c_0_46, plain, (v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.62/0.79  fof(c_0_47, plain, ![X32, X33, X34, X35, X36, X37]:((((v1_funct_1(k10_tmap_1(X32,X33,X34,X35,X36,X37))|~r4_tsep_1(X32,X34,X35)|(~v1_funct_1(X37)|~v1_funct_2(X37,u1_struct_0(X35),u1_struct_0(X33))|~v5_pre_topc(X37,X35,X33)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X33)))))|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X33))|~v5_pre_topc(X36,X34,X33)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X33)))))|~r1_tsep_1(X34,X35)|(v2_struct_0(X35)|~m1_pre_topc(X35,X32))|(v2_struct_0(X34)|~m1_pre_topc(X34,X32))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))&(v1_funct_2(k10_tmap_1(X32,X33,X34,X35,X36,X37),u1_struct_0(k1_tsep_1(X32,X34,X35)),u1_struct_0(X33))|~r4_tsep_1(X32,X34,X35)|(~v1_funct_1(X37)|~v1_funct_2(X37,u1_struct_0(X35),u1_struct_0(X33))|~v5_pre_topc(X37,X35,X33)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X33)))))|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X33))|~v5_pre_topc(X36,X34,X33)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X33)))))|~r1_tsep_1(X34,X35)|(v2_struct_0(X35)|~m1_pre_topc(X35,X32))|(v2_struct_0(X34)|~m1_pre_topc(X34,X32))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32))))&(v5_pre_topc(k10_tmap_1(X32,X33,X34,X35,X36,X37),k1_tsep_1(X32,X34,X35),X33)|~r4_tsep_1(X32,X34,X35)|(~v1_funct_1(X37)|~v1_funct_2(X37,u1_struct_0(X35),u1_struct_0(X33))|~v5_pre_topc(X37,X35,X33)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X33)))))|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X33))|~v5_pre_topc(X36,X34,X33)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X33)))))|~r1_tsep_1(X34,X35)|(v2_struct_0(X35)|~m1_pre_topc(X35,X32))|(v2_struct_0(X34)|~m1_pre_topc(X34,X32))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32))))&(m1_subset_1(k10_tmap_1(X32,X33,X34,X35,X36,X37),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X32,X34,X35)),u1_struct_0(X33))))|~r4_tsep_1(X32,X34,X35)|(~v1_funct_1(X37)|~v1_funct_2(X37,u1_struct_0(X35),u1_struct_0(X33))|~v5_pre_topc(X37,X35,X33)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X33)))))|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X34),u1_struct_0(X33))|~v5_pre_topc(X36,X34,X33)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X33)))))|~r1_tsep_1(X34,X35)|(v2_struct_0(X35)|~m1_pre_topc(X35,X32))|(v2_struct_0(X34)|~m1_pre_topc(X34,X32))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t145_tmap_1])])])])])).
% 0.62/0.79  cnf(c_0_48, negated_conjecture, (v5_pre_topc(esk7_0,esk4_0,esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.62/0.79  cnf(c_0_49, negated_conjecture, (v5_pre_topc(esk8_0,esk5_0,esk6_0)|~r1_tsep_1(esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.62/0.79  cnf(c_0_50, plain, (X5=k10_tmap_1(X3,X2,X1,X4,X6,X7)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X1,X5),X6)|~r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X4,X5),X7)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))))|~r1_tsep_1(X1,X4)|~v1_funct_1(X7)|~v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.62/0.79  cnf(c_0_51, plain, (r2_funct_2(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)), inference(er,[status(thm)],[c_0_44])).
% 0.62/0.79  cnf(c_0_52, negated_conjecture, (~v5_pre_topc(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk6_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)|~v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_17]), c_0_18]), c_0_16]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.62/0.79  cnf(c_0_53, plain, (v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r4_tsep_1(X1,X3,X4)|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~v5_pre_topc(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v5_pre_topc(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~r1_tsep_1(X3,X4)|~m1_pre_topc(X4,X1)|~m1_pre_topc(X3,X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.62/0.79  cnf(c_0_54, negated_conjecture, (v5_pre_topc(esk7_0,esk4_0,esk6_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_20])])).
% 0.62/0.79  cnf(c_0_55, negated_conjecture, (v5_pre_topc(esk8_0,esk5_0,esk6_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_20])])).
% 0.62/0.79  cnf(c_0_56, plain, (k10_tmap_1(X1,X2,X3,X4,X5,k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X6))=X6|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X4)|~r1_tsep_1(X3,X4)|~m1_pre_topc(X4,X1)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~v2_pre_topc(X2)|~r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X6),X5)|~m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X6),u1_struct_0(X4),u1_struct_0(X2))|~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X6))|~v1_funct_1(X5)|~v1_funct_1(X6)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.62/0.79  cnf(c_0_57, plain, (m1_subset_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(esk1_3(X1,X2,X3)))))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.62/0.79  cnf(c_0_58, plain, (v1_funct_1(esk2_3(X1,X2,X3))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.62/0.79  cnf(c_0_59, plain, (v1_funct_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.62/0.79  cnf(c_0_60, plain, (v1_funct_2(esk2_3(X1,X2,X3),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.62/0.79  cnf(c_0_61, plain, (v1_funct_2(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)),u1_struct_0(X3),u1_struct_0(esk1_3(X1,X2,X3)))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.62/0.79  cnf(c_0_62, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.62/0.79  cnf(c_0_63, plain, (v2_pre_topc(esk1_3(X1,X2,X3))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.62/0.79  cnf(c_0_64, plain, (l1_pre_topc(esk1_3(X1,X2,X3))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.62/0.79  cnf(c_0_65, plain, (r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk1_3(X1,X2,X3))|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.62/0.79  cnf(c_0_66, negated_conjecture, (~r4_tsep_1(esk3_0,esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)|~v1_funct_1(k10_tmap_1(esk3_0,esk6_0,esk4_0,esk5_0,esk7_0,esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_20]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_17]), c_0_18]), c_0_16]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_54]), c_0_55]), c_0_42])).
% 0.62/0.79  cnf(c_0_67, plain, (v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.62/0.79  fof(c_0_68, plain, ![X38, X39, X40]:((~r1_tsep_1(X39,X40)|~r4_tsep_1(X38,X39,X40)|r3_tsep_1(X38,X39,X40)|(v2_struct_0(X40)|~m1_pre_topc(X40,X38))|(v2_struct_0(X39)|~m1_pre_topc(X39,X38))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)))&((r1_tsep_1(X39,X40)|~r3_tsep_1(X38,X39,X40)|(v2_struct_0(X40)|~m1_pre_topc(X40,X38))|(v2_struct_0(X39)|~m1_pre_topc(X39,X38))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)))&(r4_tsep_1(X38,X39,X40)|~r3_tsep_1(X38,X39,X40)|(v2_struct_0(X40)|~m1_pre_topc(X40,X38))|(v2_struct_0(X39)|~m1_pre_topc(X39,X38))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t85_tsep_1])])])])])).
% 0.62/0.79  cnf(c_0_69, plain, (k10_tmap_1(X1,esk1_3(X1,X2,X3),X2,X3,X4,k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)))=esk2_3(X1,X2,X3)|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~r2_funct_2(u1_struct_0(X2),u1_struct_0(esk1_3(X1,X2,X3)),k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)),X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk1_3(X1,X2,X3)))))|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(esk1_3(X1,X2,X3)))|~v1_funct_1(X4)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_59]), c_0_60]), c_0_61]), c_0_62]), c_0_63]), c_0_64]), c_0_65])).
% 0.62/0.79  cnf(c_0_70, plain, (v1_funct_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.62/0.79  cnf(c_0_71, plain, (v1_funct_2(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)),u1_struct_0(X2),u1_struct_0(esk1_3(X1,X2,X3)))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.62/0.79  cnf(c_0_72, plain, (m1_subset_1(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk1_3(X1,X2,X3)))))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.62/0.79  cnf(c_0_73, negated_conjecture, (~r4_tsep_1(esk3_0,esk4_0,esk5_0)|~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_17]), c_0_18]), c_0_16]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.62/0.79  cnf(c_0_74, plain, (r4_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_tsep_1(X1,X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.62/0.79  cnf(c_0_75, negated_conjecture, (v5_pre_topc(k10_tmap_1(esk3_0,X1,esk4_0,esk5_0,X2,X3),k1_tsep_1(esk3_0,esk4_0,esk5_0),X1)|v2_struct_0(X1)|r3_tsep_1(esk3_0,esk4_0,esk5_0)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(esk5_0),u1_struct_0(X1))|~v5_pre_topc(X3,esk5_0,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))|~v1_funct_1(X2)|~v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))|~v5_pre_topc(X2,esk4_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.62/0.79  cnf(c_0_76, plain, (k10_tmap_1(X1,esk1_3(X1,X2,X3),X2,X3,k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)),k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)))=esk2_3(X1,X2,X3)|r3_tsep_1(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X3)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_51]), c_0_70]), c_0_71]), c_0_72])).
% 0.62/0.79  cnf(c_0_77, negated_conjecture, (~r3_tsep_1(esk3_0,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_17]), c_0_18]), c_0_16])).
% 0.62/0.79  cnf(c_0_78, negated_conjecture, (v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))|~v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))|~l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~m1_subset_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))|~m1_subset_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))|~v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_20]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_77]), c_0_18]), c_0_16]), c_0_17])).
% 0.62/0.79  cnf(c_0_79, negated_conjecture, (v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))|~v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))|~l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~m1_subset_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))))|~v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_57]), c_0_20]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_77]), c_0_17]), c_0_18]), c_0_16])).
% 0.62/0.79  cnf(c_0_80, negated_conjecture, (v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))|~v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))|~l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk5_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_72]), c_0_20]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_77]), c_0_17]), c_0_18]), c_0_16])).
% 0.62/0.79  cnf(c_0_81, negated_conjecture, (v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))|~v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))|~l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v1_funct_2(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(esk4_0),u1_struct_0(esk1_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_61]), c_0_20]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_77]), c_0_17]), c_0_18]), c_0_16])).
% 0.62/0.79  cnf(c_0_82, negated_conjecture, (v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))|~v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))|~l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_71]), c_0_20]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_77]), c_0_17]), c_0_18]), c_0_16])).
% 0.62/0.79  cnf(c_0_83, plain, (v5_pre_topc(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X3,esk2_3(X1,X2,X3)),X3,esk1_3(X1,X2,X3))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.62/0.79  cnf(c_0_84, negated_conjecture, (v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~v5_pre_topc(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))|~l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_20]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_77]), c_0_17]), c_0_18]), c_0_16])).
% 0.62/0.79  cnf(c_0_85, plain, (v5_pre_topc(k3_tmap_1(X1,esk1_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),X2,esk2_3(X1,X2,X3)),X2,esk1_3(X1,X2,X3))|r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.62/0.79  cnf(c_0_86, negated_conjecture, (v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_20]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_77]), c_0_17]), c_0_18]), c_0_16])).
% 0.62/0.79  cnf(c_0_87, plain, (r3_tsep_1(X1,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_funct_1(esk2_3(X1,X2,X3))|~v1_funct_2(esk2_3(X1,X2,X3),u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))|~v5_pre_topc(esk2_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),esk1_3(X1,X2,X3))|~m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(esk1_3(X1,X2,X3)))))|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.62/0.79  cnf(c_0_88, negated_conjecture, (v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v1_funct_1(k3_tmap_1(esk3_0,esk1_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk4_0,esk2_3(esk3_0,esk4_0,esk5_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_59]), c_0_20]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_77]), c_0_17]), c_0_18]), c_0_16])).
% 0.62/0.79  cnf(c_0_89, plain, (r3_tsep_1(X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v5_pre_topc(esk2_3(X1,X2,X3),k1_tsep_1(X1,X2,X3),esk1_3(X1,X2,X3))|~r1_tsep_1(X2,X3)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_87, c_0_58]), c_0_60]), c_0_62])).
% 0.62/0.79  cnf(c_0_90, negated_conjecture, (v5_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),k1_tsep_1(esk3_0,esk4_0,esk5_0),esk1_3(esk3_0,esk4_0,esk5_0))|v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_70]), c_0_20]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_77]), c_0_17]), c_0_18]), c_0_16])).
% 0.62/0.79  cnf(c_0_91, negated_conjecture, (v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~l1_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_20]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_77]), c_0_17]), c_0_18]), c_0_16])).
% 0.62/0.79  cnf(c_0_92, negated_conjecture, (v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))|~v2_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_64]), c_0_20]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_77]), c_0_17]), c_0_18]), c_0_16])).
% 0.62/0.79  cnf(c_0_93, negated_conjecture, (v2_struct_0(esk1_3(esk3_0,esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_63]), c_0_20]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_77]), c_0_17]), c_0_18]), c_0_16])).
% 0.62/0.79  cnf(c_0_94, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_93]), c_0_20]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_77]), c_0_17]), c_0_18]), c_0_16]), ['proof']).
% 0.62/0.79  # SZS output end CNFRefutation
% 0.62/0.79  # Proof object total steps             : 95
% 0.62/0.79  # Proof object clause steps            : 80
% 0.62/0.79  # Proof object formula steps           : 15
% 0.62/0.79  # Proof object conjectures             : 55
% 0.62/0.79  # Proof object clause conjectures      : 52
% 0.62/0.79  # Proof object formula conjectures     : 3
% 0.62/0.79  # Proof object initial clauses used    : 44
% 0.62/0.79  # Proof object initial formulas used   : 7
% 0.62/0.79  # Proof object generating inferences   : 22
% 0.62/0.79  # Proof object simplifying inferences  : 256
% 0.62/0.79  # Training examples: 0 positive, 0 negative
% 0.62/0.79  # Parsed axioms                        : 7
% 0.62/0.79  # Removed by relevancy pruning/SinE    : 0
% 0.62/0.79  # Initial clauses                      : 62
% 0.62/0.79  # Removed in clause preprocessing      : 3
% 0.62/0.79  # Initial clauses in saturation        : 59
% 0.62/0.79  # Processed clauses                    : 1187
% 0.62/0.79  # ...of these trivial                  : 0
% 0.62/0.79  # ...subsumed                          : 876
% 0.62/0.79  # ...remaining for further processing  : 311
% 0.62/0.79  # Other redundant clauses eliminated   : 5
% 0.62/0.79  # Clauses deleted for lack of memory   : 0
% 0.62/0.79  # Backward-subsumed                    : 38
% 0.62/0.79  # Backward-rewritten                   : 12
% 0.62/0.79  # Generated clauses                    : 3401
% 0.62/0.79  # ...of the previous two non-trivial   : 3364
% 0.62/0.79  # Contextual simplify-reflections      : 307
% 0.62/0.79  # Paramodulations                      : 3384
% 0.62/0.79  # Factorizations                       : 12
% 0.62/0.79  # Equation resolutions                 : 5
% 0.62/0.79  # Propositional unsat checks           : 0
% 0.62/0.79  #    Propositional check models        : 0
% 0.62/0.79  #    Propositional check unsatisfiable : 0
% 0.62/0.79  #    Propositional clauses             : 0
% 0.62/0.79  #    Propositional clauses after purity: 0
% 0.62/0.79  #    Propositional unsat core size     : 0
% 0.62/0.79  #    Propositional preprocessing time  : 0.000
% 0.62/0.79  #    Propositional encoding time       : 0.000
% 0.62/0.79  #    Propositional solver time         : 0.000
% 0.62/0.79  #    Success case prop preproc time    : 0.000
% 0.62/0.79  #    Success case prop encoding time   : 0.000
% 0.62/0.79  #    Success case prop solver time     : 0.000
% 0.62/0.79  # Current number of processed clauses  : 201
% 0.62/0.79  #    Positive orientable unit clauses  : 6
% 0.62/0.79  #    Positive unorientable unit clauses: 0
% 0.62/0.79  #    Negative unit clauses             : 4
% 0.62/0.80  #    Non-unit-clauses                  : 191
% 0.62/0.80  # Current number of unprocessed clauses: 2270
% 0.62/0.80  # ...number of literals in the above   : 64530
% 0.62/0.80  # Current number of archived formulas  : 0
% 0.62/0.80  # Current number of archived clauses   : 105
% 0.62/0.80  # Clause-clause subsumption calls (NU) : 130190
% 0.62/0.80  # Rec. Clause-clause subsumption calls : 4641
% 0.62/0.80  # Non-unit clause-clause subsumptions  : 1203
% 0.62/0.80  # Unit Clause-clause subsumption calls : 193
% 0.62/0.80  # Rewrite failures with RHS unbound    : 0
% 0.62/0.80  # BW rewrite match attempts            : 2
% 0.62/0.80  # BW rewrite match successes           : 2
% 0.62/0.80  # Condensation attempts                : 0
% 0.62/0.80  # Condensation successes               : 0
% 0.62/0.80  # Termbank termtop insertions          : 467270
% 0.62/0.80  
% 0.62/0.80  # -------------------------------------------------
% 0.62/0.80  # User time                : 0.450 s
% 0.62/0.80  # System time              : 0.004 s
% 0.62/0.80  # Total time               : 0.455 s
% 0.62/0.80  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
