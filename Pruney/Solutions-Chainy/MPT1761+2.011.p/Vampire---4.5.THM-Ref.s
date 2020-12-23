%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 377 expanded)
%              Number of leaves         :   16 ( 191 expanded)
%              Depth                    :   21
%              Number of atoms          :  499 (5685 expanded)
%              Number of equality atoms :   64 ( 489 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,(
    k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK5) ),
    inference(superposition,[],[f97,f71])).

fof(f71,plain,(
    k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5) ),
    inference(resolution,[],[f70,f48])).

fof(f48,plain,(
    r2_hidden(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    & r2_hidden(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f13,f31,f30,f29,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)
                            & r2_hidden(X5,u1_struct_0(X2))
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X4),X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X4),X5)
                        & r2_hidden(X5,u1_struct_0(X2))
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,X4),X5)
                      & r2_hidden(X5,u1_struct_0(X2))
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,X4),X5)
                    & r2_hidden(X5,u1_struct_0(X2))
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,X3,sK2,X4),X5)
                  & r2_hidden(X5,u1_struct_0(sK2))
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(sK2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,X3,sK2,X4),X5)
                & r2_hidden(X5,u1_struct_0(sK2))
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & m1_pre_topc(sK2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5)
              & r2_hidden(X5,u1_struct_0(sK2))
              & m1_subset_1(X5,u1_struct_0(sK3)) )
          & m1_pre_topc(sK2,sK3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5)
            & r2_hidden(X5,u1_struct_0(sK2))
            & m1_subset_1(X5,u1_struct_0(sK3)) )
        & m1_pre_topc(sK2,sK3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5)
          & r2_hidden(X5,u1_struct_0(sK2))
          & m1_subset_1(X5,u1_struct_0(sK3)) )
      & m1_pre_topc(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X5] :
        ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5)
        & r2_hidden(X5,u1_struct_0(sK2))
        & m1_subset_1(X5,u1_struct_0(sK3)) )
   => ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
      & r2_hidden(sK5,u1_struct_0(sK2))
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ( r2_hidden(X5,u1_struct_0(X2))
                               => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ( r2_hidden(X5,u1_struct_0(X2))
                             => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tmap_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k1_funct_1(k7_relat_1(sK4,X0),X1) = k1_funct_1(sK4,X1) ) ),
    inference(resolution,[],[f69,f67])).

fof(f67,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f63,f45])).

fof(f45,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f50,f54])).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK4)
      | k1_funct_1(k7_relat_1(sK4,X1),X0) = k1_funct_1(sK4,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f55,f43])).

fof(f43,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,X1)
      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

fof(f97,plain,(
    k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k1_funct_1(sK4,sK5) ),
    inference(backward_demodulation,[],[f84,f96])).

fof(f96,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f95,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f95,plain,
    ( v2_struct_0(sK0)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f94,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f94,plain,
    ( v2_struct_0(sK1)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f93,f40])).

fof(f40,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f93,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f92,f46])).

fof(f46,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(sK1)
      | k7_relat_1(sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f91,f35])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f91,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | k7_relat_1(sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f90,f34])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK3)
      | k7_relat_1(sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f89,f42])).

fof(f42,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK3,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,sK3)
      | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k7_relat_1(sK4,u1_struct_0(X0))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f88,f45])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ m1_pre_topc(X0,sK3)
      | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k7_relat_1(sK4,u1_struct_0(X0))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f87,f38])).

fof(f38,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k7_relat_1(sK4,u1_struct_0(X0))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f86,f37])).

fof(f37,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(sK1)
      | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k7_relat_1(sK4,u1_struct_0(X0))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(forward_demodulation,[],[f85,f73])).

fof(f73,plain,(
    ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) ),
    inference(resolution,[],[f72,f45])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ) ),
    inference(resolution,[],[f58,f43])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK3)
      | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f79,f44])).

fof(f44,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ m1_pre_topc(X0,X1)
      | k3_tmap_1(X3,X2,X1,X0,sK4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X3)
      | ~ m1_pre_topc(X1,X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f53,f43])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f84,plain,(
    k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k1_funct_1(sK4,sK5) ),
    inference(backward_demodulation,[],[f49,f83])).

fof(f83,plain,(
    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5) ),
    inference(resolution,[],[f82,f48])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK2))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5) ) ),
    inference(resolution,[],[f81,f46])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,sK3)
      | ~ r2_hidden(X0,u1_struct_0(X1))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5) ) ),
    inference(resolution,[],[f80,f62])).

fof(f62,plain,(
    l1_pre_topc(sK3) ),
    inference(resolution,[],[f59,f42])).

fof(f59,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f51,f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK3)
      | ~ r2_hidden(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK3)
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5) ) ),
    inference(resolution,[],[f78,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5)
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f77,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f77,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5) ),
    inference(resolution,[],[f76,f47])).

fof(f47,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | k1_funct_1(sK4,X0) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0)
      | v1_xboole_0(u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f75,f44])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | k1_funct_1(sK4,X0) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0)
      | v1_xboole_0(u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f74,f45])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X0,X1)
      | ~ v1_funct_2(sK4,X1,X2)
      | k1_funct_1(sK4,X0) = k3_funct_2(X1,X2,sK4,X0)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f57,f43])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f49,plain,(
    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:28:22 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.21/0.47  % (4970)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.47  % (4972)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.47  % (4971)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.47  % (4965)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.48  % (4965)Refutation not found, incomplete strategy% (4965)------------------------------
% 0.21/0.48  % (4965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (4965)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (4965)Memory used [KB]: 10618
% 0.21/0.48  % (4965)Time elapsed: 0.076 s
% 0.21/0.48  % (4965)------------------------------
% 0.21/0.48  % (4965)------------------------------
% 0.21/0.48  % (4970)Refutation not found, incomplete strategy% (4970)------------------------------
% 0.21/0.48  % (4970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (4970)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (4970)Memory used [KB]: 10746
% 0.21/0.48  % (4970)Time elapsed: 0.078 s
% 0.21/0.48  % (4970)------------------------------
% 0.21/0.48  % (4970)------------------------------
% 0.21/0.48  % (4963)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.48  % (4964)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.49  % (4980)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.49  % (4962)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.49  % (4971)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f98])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK5)),
% 0.21/0.49    inference(superposition,[],[f97,f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5)),
% 0.21/0.49    inference(resolution,[],[f70,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    r2_hidden(sK5,u1_struct_0(sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    (((((k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) & r2_hidden(sK5,u1_struct_0(sK2)) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f13,f31,f30,f29,f28,f27,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X4),X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,X1,X3,X2,X4),X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,X4),X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,X3,X2,X4),X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,X3,sK2,X4),X5) & r2_hidden(X5,u1_struct_0(sK2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ? [X3] : (? [X4] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,X3,sK2,X4),X5) & r2_hidden(X5,u1_struct_0(sK2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5) & r2_hidden(X5,u1_struct_0(sK2)) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ? [X4] : (? [X5] : (k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5) & r2_hidden(X5,u1_struct_0(sK2)) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5) & r2_hidden(X5,u1_struct_0(sK2)) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ? [X5] : (k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5) & r2_hidden(X5,u1_struct_0(sK2)) & m1_subset_1(X5,u1_struct_0(sK3))) => (k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) & r2_hidden(sK5,u1_struct_0(sK2)) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : ((k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f10])).
% 0.21/0.49  fof(f10,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tmap_1)).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k1_funct_1(k7_relat_1(sK4,X0),X1) = k1_funct_1(sK4,X1)) )),
% 0.21/0.49    inference(resolution,[],[f69,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    v1_relat_1(sK4)),
% 0.21/0.49    inference(resolution,[],[f63,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 0.21/0.49    inference(resolution,[],[f50,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(sK4) | k1_funct_1(k7_relat_1(sK4,X1),X0) = k1_funct_1(sK4,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(resolution,[],[f55,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    v1_funct_1(sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X0,X1) | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k1_funct_1(sK4,sK5)),
% 0.21/0.49    inference(backward_demodulation,[],[f84,f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))),
% 0.21/0.49    inference(resolution,[],[f95,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    v2_struct_0(sK0) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))),
% 0.21/0.49    inference(resolution,[],[f94,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ~v2_struct_0(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    v2_struct_0(sK1) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f93,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    m1_pre_topc(sK2,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ~m1_pre_topc(sK2,sK0) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) | v2_struct_0(sK1) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f92,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    m1_pre_topc(sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK3) | v2_struct_0(sK1) | k7_relat_1(sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f91,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_pre_topc(sK0) | k7_relat_1(sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) | v2_struct_0(sK1) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f90,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK3) | k7_relat_1(sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f89,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    m1_pre_topc(sK3,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,sK3) | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k7_relat_1(sK4,u1_struct_0(X0)) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.49    inference(resolution,[],[f88,f45])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X0,sK3) | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k7_relat_1(sK4,u1_struct_0(X0)) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.49    inference(resolution,[],[f87,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    l1_pre_topc(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(sK1) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k7_relat_1(sK4,u1_struct_0(X0)) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.49    inference(resolution,[],[f86,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    v2_pre_topc(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_pre_topc(sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(sK1) | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k7_relat_1(sK4,u1_struct_0(X0)) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f85,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0)) )),
% 0.21/0.49    inference(resolution,[],[f72,f45])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)) )),
% 0.21/0.49    inference(resolution,[],[f58,f43])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK3) | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.49    inference(resolution,[],[f79,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X0,X1) | k3_tmap_1(X3,X2,X1,X0,sK4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,X3) | ~m1_pre_topc(X1,X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 0.21/0.49    inference(resolution,[],[f53,f43])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k1_funct_1(sK4,sK5)),
% 0.21/0.49    inference(backward_demodulation,[],[f49,f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5)),
% 0.21/0.49    inference(resolution,[],[f82,f48])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK2)) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5)) )),
% 0.21/0.49    inference(resolution,[],[f81,f46])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,sK3) | ~r2_hidden(X0,u1_struct_0(X1)) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5)) )),
% 0.21/0.49    inference(resolution,[],[f80,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    l1_pre_topc(sK3)),
% 0.21/0.49    inference(resolution,[],[f59,f42])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 0.21/0.49    inference(resolution,[],[f51,f35])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(sK3) | ~r2_hidden(X0,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5)) )),
% 0.21/0.49    inference(resolution,[],[f78,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5) | ~r2_hidden(X1,X0)) )),
% 0.21/0.49    inference(resolution,[],[f77,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    v1_xboole_0(u1_struct_0(sK3)) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5)),
% 0.21/0.49    inference(resolution,[],[f76,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | k1_funct_1(sK4,X0) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) | v1_xboole_0(u1_struct_0(sK3))) )),
% 0.21/0.49    inference(resolution,[],[f75,f44])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | k1_funct_1(sK4,X0) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) | v1_xboole_0(u1_struct_0(sK3))) )),
% 0.21/0.49    inference(resolution,[],[f74,f45])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,X1) | ~v1_funct_2(sK4,X1,X2) | k1_funct_1(sK4,X0) = k3_funct_2(X1,X2,sK4,X0) | v1_xboole_0(X1)) )),
% 0.21/0.49    inference(resolution,[],[f57,f43])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (4971)------------------------------
% 0.21/0.49  % (4971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (4971)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (4971)Memory used [KB]: 1791
% 0.21/0.49  % (4971)Time elapsed: 0.085 s
% 0.21/0.49  % (4971)------------------------------
% 0.21/0.49  % (4971)------------------------------
% 0.21/0.49  % (4961)Success in time 0.131 s
%------------------------------------------------------------------------------
