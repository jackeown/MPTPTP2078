%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 822 expanded)
%              Number of leaves         :   13 ( 425 expanded)
%              Depth                    :   22
%              Number of atoms          :  539 (12907 expanded)
%              Number of equality atoms :   55 (1094 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f539,plain,(
    $false ),
    inference(subsumption_resolution,[],[f515,f527])).

fof(f527,plain,(
    ~ m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f526,f500])).

fof(f500,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f499,f35])).

fof(f35,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    & r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f10,f26,f25,f24,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                            & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
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
                          ( k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5)
                          & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
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

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5)
                        & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
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
                      ( k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X4),X5)
                      & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5),u1_struct_0(X2))
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
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

fof(f23,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X4),X5)
                    & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5),u1_struct_0(X2))
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
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
                  ( k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X4),X5)
                  & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5),u1_struct_0(sK2))
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
              & m1_pre_topc(sK2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X4),X5)
                & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5),u1_struct_0(sK2))
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
            & m1_pre_topc(sK2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),X4,X5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5)
              & r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),X4,X5),u1_struct_0(sK2))
              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_pre_topc(sK2,sK3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

% (31790)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
fof(f25,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),X4,X5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5)
            & r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),X4,X5),u1_struct_0(sK2))
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_pre_topc(sK2,sK3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5)
          & r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X5),u1_struct_0(sK2))
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_pre_topc(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X5] :
        ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5)
        & r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X5),u1_struct_0(sK2))
        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
      & r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2))
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
                              ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                             => ( r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))
                               => k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                           => ( r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))
                             => k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tmap_1)).

fof(f499,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f308,f41])).

fof(f41,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f308,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,sK0)
      | k7_relat_1(sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) ) ),
    inference(subsumption_resolution,[],[f307,f28])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f307,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,sK0)
      | k7_relat_1(sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f306,f29])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f306,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,sK0)
      | k7_relat_1(sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f305,f30])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f305,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,sK0)
      | k7_relat_1(sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f270,f37])).

fof(f37,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f270,plain,(
    ! [X6,X7] :
      ( ~ m1_pre_topc(sK3,X6)
      | ~ m1_pre_topc(X7,sK3)
      | ~ m1_pre_topc(X7,X6)
      | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k7_relat_1(sK4,u1_struct_0(X7))
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(backward_demodulation,[],[f261,f269])).

fof(f269,plain,(
    ! [X8] : k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X8) = k7_relat_1(sK4,X8) ),
    inference(subsumption_resolution,[],[f266,f38])).

fof(f38,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f266,plain,(
    ! [X8] :
      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X8) = k7_relat_1(sK4,X8)
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f40,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f40,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f261,plain,(
    ! [X6,X7] :
      ( k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X7))
      | ~ m1_pre_topc(X7,sK3)
      | ~ m1_pre_topc(X7,X6)
      | ~ m1_pre_topc(sK3,X6)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f260,f31])).

fof(f31,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f260,plain,(
    ! [X6,X7] :
      ( k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X7))
      | ~ m1_pre_topc(X7,sK3)
      | ~ m1_pre_topc(X7,X6)
      | ~ m1_pre_topc(sK3,X6)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f259,f32])).

fof(f32,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f259,plain,(
    ! [X6,X7] :
      ( k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X7))
      | ~ m1_pre_topc(X7,sK3)
      | ~ m1_pre_topc(X7,X6)
      | ~ m1_pre_topc(sK3,X6)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f258,f33])).

fof(f33,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f258,plain,(
    ! [X6,X7] :
      ( k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X7))
      | ~ m1_pre_topc(X7,sK3)
      | ~ m1_pre_topc(X7,X6)
      | ~ m1_pre_topc(sK3,X6)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f257,f38])).

fof(f257,plain,(
    ! [X6,X7] :
      ( k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X7))
      | ~ m1_pre_topc(X7,sK3)
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X7,X6)
      | ~ m1_pre_topc(sK3,X6)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f241,f40])).

fof(f241,plain,(
    ! [X6,X7] :
      ( k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X7))
      | ~ m1_pre_topc(X7,sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X7,X6)
      | ~ m1_pre_topc(sK3,X6)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f39,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f39,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f526,plain,(
    ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f502,f275])).

fof(f275,plain,(
    k10_relat_1(sK4,sK5) = k10_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) ),
    inference(subsumption_resolution,[],[f274,f268])).

fof(f268,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f40,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f274,plain,
    ( k10_relat_1(sK4,sK5) = k10_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f273,f38])).

fof(f273,plain,
    ( k10_relat_1(sK4,sK5) = k10_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f271,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
      | ~ r1_tarski(k10_relat_1(X0,X2),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
          | ~ r1_tarski(k10_relat_1(X0,X2),X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
          | ~ r1_tarski(k10_relat_1(X0,X2),X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f271,plain,(
    r1_tarski(k10_relat_1(sK4,sK5),u1_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f43,f267])).

fof(f267,plain,(
    ! [X9] : k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X9) = k10_relat_1(sK4,X9) ),
    inference(resolution,[],[f40,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f43,plain,(
    r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f502,plain,
    ( k10_relat_1(sK4,sK5) != k10_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f276,f500])).

fof(f276,plain,
    ( k10_relat_1(sK4,sK5) != k10_relat_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f272,f48])).

fof(f272,plain,(
    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k10_relat_1(sK4,sK5) ),
    inference(backward_demodulation,[],[f44,f267])).

fof(f44,plain,(
    k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f515,plain,(
    m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f396,f500])).

fof(f396,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(resolution,[],[f298,f35])).

fof(f298,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) ) ),
    inference(subsumption_resolution,[],[f297,f28])).

fof(f297,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f296,f29])).

fof(f296,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f295,f30])).

fof(f295,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f256,f37])).

fof(f256,plain,(
    ! [X4,X5] :
      ( ~ m1_pre_topc(sK3,X4)
      | ~ m1_pre_topc(X5,X4)
      | m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f255,f31])).

fof(f255,plain,(
    ! [X4,X5] :
      ( m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X5,X4)
      | ~ m1_pre_topc(sK3,X4)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f254,f32])).

fof(f254,plain,(
    ! [X4,X5] :
      ( m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X5,X4)
      | ~ m1_pre_topc(sK3,X4)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f253,f33])).

fof(f253,plain,(
    ! [X4,X5] :
      ( m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X5,X4)
      | ~ m1_pre_topc(sK3,X4)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f252,f38])).

fof(f252,plain,(
    ! [X4,X5] :
      ( m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X5,X4)
      | ~ m1_pre_topc(sK3,X4)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f240,f40])).

fof(f240,plain,(
    ! [X4,X5] :
      ( m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X5,X4)
      | ~ m1_pre_topc(sK3,X4)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f39,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:58:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (31788)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.50  % (31780)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (31782)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (31780)Refutation not found, incomplete strategy% (31780)------------------------------
% 0.21/0.50  % (31780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (31780)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (31780)Memory used [KB]: 10618
% 0.21/0.50  % (31780)Time elapsed: 0.083 s
% 0.21/0.50  % (31780)------------------------------
% 0.21/0.50  % (31780)------------------------------
% 0.21/0.51  % (31796)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (31794)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.51  % (31792)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (31779)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (31778)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (31777)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (31795)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (31787)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  % (31797)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.52  % (31791)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.52  % (31783)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.52  % (31786)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.52  % (31784)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (31787)Refutation not found, incomplete strategy% (31787)------------------------------
% 0.21/0.52  % (31787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31787)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31787)Memory used [KB]: 10618
% 0.21/0.52  % (31787)Time elapsed: 0.108 s
% 0.21/0.52  % (31787)------------------------------
% 0.21/0.52  % (31787)------------------------------
% 0.21/0.52  % (31785)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.52  % (31788)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f539,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f515,f527])).
% 0.21/0.52  fof(f527,plain,(
% 0.21/0.52    ~m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.21/0.52    inference(forward_demodulation,[],[f526,f500])).
% 0.21/0.52  fof(f500,plain,(
% 0.21/0.52    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))),
% 0.21/0.52    inference(subsumption_resolution,[],[f499,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    m1_pre_topc(sK2,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    (((((k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) & r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f10,f26,f25,f24,f23,f22,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5),u1_struct_0(sK2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,sK2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5),u1_struct_0(sK2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),X4,X5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),X4,X5),u1_struct_0(sK2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  % (31790)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),X4,X5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),X4,X5),u1_struct_0(sK2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5) & r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X5),u1_struct_0(sK2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ? [X5] : (k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X5) & r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X5),u1_struct_0(sK2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) => (k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) & r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : ((k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f7])).
% 0.21/0.52  fof(f7,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tmap_1)).
% 0.21/0.52  fof(f499,plain,(
% 0.21/0.52    ~m1_pre_topc(sK2,sK0) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))),
% 0.21/0.52    inference(resolution,[],[f308,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    m1_pre_topc(sK2,sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f308,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK0) | k7_relat_1(sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f307,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ~v2_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f307,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK0) | k7_relat_1(sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) | v2_struct_0(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f306,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f306,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK0) | k7_relat_1(sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f305,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f305,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK0) | k7_relat_1(sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.52    inference(resolution,[],[f270,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    m1_pre_topc(sK3,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f270,plain,(
% 0.21/0.52    ( ! [X6,X7] : (~m1_pre_topc(sK3,X6) | ~m1_pre_topc(X7,sK3) | ~m1_pre_topc(X7,X6) | k3_tmap_1(X6,sK1,sK3,X7,sK4) = k7_relat_1(sK4,u1_struct_0(X7)) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 0.21/0.52    inference(backward_demodulation,[],[f261,f269])).
% 0.21/0.52  fof(f269,plain,(
% 0.21/0.52    ( ! [X8] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X8) = k7_relat_1(sK4,X8)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f266,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    v1_funct_1(sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f266,plain,(
% 0.21/0.52    ( ! [X8] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X8) = k7_relat_1(sK4,X8) | ~v1_funct_1(sK4)) )),
% 0.21/0.52    inference(resolution,[],[f40,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f261,plain,(
% 0.21/0.52    ( ! [X6,X7] : (k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X7)) | ~m1_pre_topc(X7,sK3) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f260,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ~v2_struct_0(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f260,plain,(
% 0.21/0.52    ( ! [X6,X7] : (k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X7)) | ~m1_pre_topc(X7,sK3) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(sK3,X6) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f259,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    v2_pre_topc(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f259,plain,(
% 0.21/0.52    ( ! [X6,X7] : (k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X7)) | ~m1_pre_topc(X7,sK3) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(sK3,X6) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f258,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    l1_pre_topc(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f258,plain,(
% 0.21/0.52    ( ! [X6,X7] : (k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X7)) | ~m1_pre_topc(X7,sK3) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f257,f38])).
% 0.21/0.52  fof(f257,plain,(
% 0.21/0.52    ( ! [X6,X7] : (k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X7)) | ~m1_pre_topc(X7,sK3) | ~v1_funct_1(sK4) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f241,f40])).
% 0.21/0.52  fof(f241,plain,(
% 0.21/0.52    ( ! [X6,X7] : (k3_tmap_1(X6,sK1,sK3,X7,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X7)) | ~m1_pre_topc(X7,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(sK4) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 0.21/0.52    inference(resolution,[],[f39,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f526,plain,(
% 0.21/0.52    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.21/0.52    inference(subsumption_resolution,[],[f502,f275])).
% 0.21/0.52  fof(f275,plain,(
% 0.21/0.52    k10_relat_1(sK4,sK5) = k10_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f274,f268])).
% 0.21/0.52  fof(f268,plain,(
% 0.21/0.52    v1_relat_1(sK4)),
% 0.21/0.52    inference(resolution,[],[f40,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.52  fof(f274,plain,(
% 0.21/0.52    k10_relat_1(sK4,sK5) = k10_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) | ~v1_relat_1(sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f273,f38])).
% 0.21/0.52  fof(f273,plain,(
% 0.21/0.52    k10_relat_1(sK4,sK5) = k10_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.52    inference(resolution,[],[f271,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 0.21/0.52  fof(f271,plain,(
% 0.21/0.52    r1_tarski(k10_relat_1(sK4,sK5),u1_struct_0(sK2))),
% 0.21/0.52    inference(backward_demodulation,[],[f43,f267])).
% 0.21/0.52  fof(f267,plain,(
% 0.21/0.52    ( ! [X9] : (k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X9) = k10_relat_1(sK4,X9)) )),
% 0.21/0.52    inference(resolution,[],[f40,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f502,plain,(
% 0.21/0.52    k10_relat_1(sK4,sK5) != k10_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.21/0.52    inference(backward_demodulation,[],[f276,f500])).
% 0.21/0.52  fof(f276,plain,(
% 0.21/0.52    k10_relat_1(sK4,sK5) != k10_relat_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.21/0.52    inference(superposition,[],[f272,f48])).
% 0.21/0.52  fof(f272,plain,(
% 0.21/0.52    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k10_relat_1(sK4,sK5)),
% 0.21/0.52    inference(backward_demodulation,[],[f44,f267])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f515,plain,(
% 0.21/0.52    m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.21/0.52    inference(backward_demodulation,[],[f396,f500])).
% 0.21/0.52  fof(f396,plain,(
% 0.21/0.52    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.21/0.52    inference(resolution,[],[f298,f35])).
% 0.21/0.52  fof(f298,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f297,f28])).
% 0.21/0.52  fof(f297,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | v2_struct_0(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f296,f29])).
% 0.21/0.52  fof(f296,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f295,f30])).
% 0.21/0.52  fof(f295,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.52    inference(resolution,[],[f256,f37])).
% 0.21/0.52  fof(f256,plain,(
% 0.21/0.52    ( ! [X4,X5] : (~m1_pre_topc(sK3,X4) | ~m1_pre_topc(X5,X4) | m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f255,f31])).
% 0.21/0.52  fof(f255,plain,(
% 0.21/0.52    ( ! [X4,X5] : (m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~m1_pre_topc(X5,X4) | ~m1_pre_topc(sK3,X4) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f254,f32])).
% 0.21/0.52  fof(f254,plain,(
% 0.21/0.52    ( ! [X4,X5] : (m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~m1_pre_topc(X5,X4) | ~m1_pre_topc(sK3,X4) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f253,f33])).
% 0.21/0.52  fof(f253,plain,(
% 0.21/0.52    ( ! [X4,X5] : (m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~m1_pre_topc(X5,X4) | ~m1_pre_topc(sK3,X4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f252,f38])).
% 0.21/0.52  fof(f252,plain,(
% 0.21/0.52    ( ! [X4,X5] : (m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v1_funct_1(sK4) | ~m1_pre_topc(X5,X4) | ~m1_pre_topc(sK3,X4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f240,f40])).
% 0.21/0.52  fof(f240,plain,(
% 0.21/0.52    ( ! [X4,X5] : (m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(sK4) | ~m1_pre_topc(X5,X4) | ~m1_pre_topc(sK3,X4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.21/0.52    inference(resolution,[],[f39,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (31788)------------------------------
% 0.21/0.52  % (31788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31788)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (31788)Memory used [KB]: 2174
% 0.21/0.52  % (31788)Time elapsed: 0.086 s
% 0.21/0.52  % (31788)------------------------------
% 0.21/0.52  % (31788)------------------------------
% 0.21/0.52  % (31771)Success in time 0.158 s
%------------------------------------------------------------------------------
